-- Prove2me | Definitions.Def_Kepler_LPTemplateModel
-- name    : Kepler_LPTemplateModel
-- status  : Definition
-- author  : @Minghui
-- created : 2026-09-27T02:57:20.715161+00:00
-- url     : https://prove2.me/theorems/0b8ba14e-e929-4c25-b75a-51237f3e7577
-- title:
--   Indexed affine row templates
-- statement:
--   Let $L$ be any finite ordered list of finite lists of natural labels. Each face $[v_0,\ldots,v_{k-1}]$ contributes the ordered cyclic pairs $(v_i,v_{i+1\bmod k})$; empty faces contribute none and singleton faces contribute loops. Concatenating these lists gives the dart list, with multiplicities. The node list is the flattened label list after deleting every occurrence that has a later equal occurrence, so distinct labels retain their last-occurrence order. An index value is tagged as one node, one ordered dart pair, a list of dart pairs, or a list of nodes. There are five index pools: the node list tagged individually; the dart list tagged individually; each face's entire dart list; for each distinct node, the list of all dart occurrences whose first coordinate is that node; and individual darts of the faces whose length equals a specified natural number, including the possible size $0$. An address is a finite expression formed from bound-dart, bound-node, bound-face, bound-node-darts, all-nodes, next, previous, edge, first, chosen-dart and face-of constructors. The first two bound forms require the corresponding singleton tag; both bound-face and bound-node-darts accept exactly the dart-list tag, without distinguishing those two meanings. All-nodes ignores the bound index and returns the node list. For a dart $d$, next and previous use its first occurrence in the first containing face's dart list, wrapping cyclically, and return $d$ if no lookup succeeds. Edge reverses the pair and first returns its initial label. Chosen-dart requires a dart list and returns its first entry, failing on the empty list. Face-of requires a dart and returns the dart list of its first containing face, failing if that list is empty. Every other address type mismatch fails, and failure of a subexpression propagates. A syntactic variable is a node kind with a label, a dart kind with an ordered pair, or a face kind with a pair list. Node kinds are yn, ln and rho; dart kinds are azim, azim2, azim3, rhazim, rhazim2, rhazim3, ye, y1 through y9, and y4prime; face kinds are sol and tau. A feature consists of such a kind and an address and requests one node, dart or face variable, or the list of node or dart variables over the evaluated node-list or dart-list address. Instantiation fails on the wrong tag; a sum over an empty accepted list succeeds with no variables, and repeated list entries are retained. A row template consists of an arbitrary name string, a Boolean standard-only flag, a natural precision, an index pool, an ordered list of integer-coefficient/feature pairs, and an integer right-hand side. An affine row consists of an ordered list of rational-coefficient/variable pairs and a rational right-hand side. To instantiate a template at a natural pool index $i$, fetch the $i$th pool value, instantiate every feature there, replace each resulting variable by a term with that feature's same integer coefficient cast to $\mathbb Q$, and concatenate the term lists in order; cast the right-hand side to $\mathbb Q$. An out-of-range index or any failed feature makes the whole operation fail. No coefficient is divided by a precision factor, the name, flag and precision are not validated or otherwise used by this operation, repeated variables are not combined, and an empty term list is allowed. There is no assumption that $L$ is nonempty or represents a hypermap, and successful instantiation alone asserts neither address validity nor any row inequality.
--
--   **Source and scope.** Primary §9; formal_lp/hypermap/main/prove_flyspeck_lp.hl:263–281 and the source sequence/list enumerations. Typed variables, exact affine rows and source index-pool semantics.
-- source:
--   Hales et al. (2017), A Formal Proof of the Kepler Conjecture, https://doi.org/10.1017/fmp.2017.1; Primary §9; formal_lp/hypermap/main/prove_flyspeck_lp.hl:263–281 and the source sequence/list enumerations. Typed variables, exact affine rows and source index-pool semantics.; https://github.com/flyspeck/flyspeck/tree/1ce0353008eba83d3c76ae9a25c3c242e4802d53

/-
Flyspeck source material is reproduced and adapted under this license:
MIT License

Copyright (c) 2014 Thomas C. Hales

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

-/
import Definitions.Def_Kepler_LPGeometricVariables
import Definitions.Def_Kepler_LPLinearSystem

set_option autoImplicit false
open scoped BigOperators

namespace KeplerMission.SourceLP

/-- SSReflect `undup`: retain the last occurrence, preserving that order. -/
def sourceNodes (L : FaceList) : List ℕ :=
  L.flatten.foldr (fun v acc => if v ∈ acc then acc else v :: acc) []

inductive IndexPool where
  | nodes | darts | faces | nodeDarts | dartsOfSize (size : ℕ)
  deriving DecidableEq, Repr

inductive IndexValue where
  | node (v : ℕ)
  | dart (d : ℕ × ℕ)
  | darts (ds : List (ℕ × ℕ))
  | nodes (vs : List ℕ)
  deriving DecidableEq, Repr

/-- Ordered source indexing pools, evaluated on the current refined face list. -/
def IndexPool.values (L : FaceList) : IndexPool → List IndexValue
  | .nodes => (sourceNodes L).map .node
  | .darts => L.darts.map .dart
  | .faces => (L.map FaceList.faceDarts).map .darts
  | .nodeDarts => (sourceNodes L).map (fun v =>
      .darts (L.darts.filter (fun d => d.1 = v)))
  | .dartsOfSize n => ((L.filter (fun f => f.length = n)).flatMap FaceList.faceDarts).map .dart

/-- Only the address operations occurring in final source row templates. -/
inductive Address where
  | boundDart | boundNode | boundFace | boundNodeDarts | allNodes
  | next (a : Address) | prev (a : Address) | edge (a : Address)
  | first (a : Address) | chosenDart (a : Address) | faceOf (a : Address)
  deriving DecidableEq, Repr

def Address.eval (L : FaceList) (index : IndexValue) : Address → Option IndexValue
  | .boundDart => match index with | .dart d => some (.dart d) | _ => none
  | .boundNode => match index with | .node v => some (.node v) | _ => none
  | .boundFace | .boundNodeDarts =>
      match index with | .darts ds => some (.darts ds) | _ => none
  | .allNodes => some (.nodes (sourceNodes L))
  | .next a => do
      let .dart d ← a.eval L index | none
      return .dart (nextDart L d)
  | .prev a => do
      let .dart d ← a.eval L index | none
      return .dart (previousDart L d)
  | .edge a => do
      let .dart d ← a.eval L index | none
      return .dart (d.2, d.1)
  | .first a => do
      let .dart d ← a.eval L index | none
      return .node d.1
  | .chosenDart a => do
      let .darts ds ← a.eval L index | none
      return .dart (← ds.head?)
  | .faceOf a => do
      let .dart d ← a.eval L index | none
      let face := faceDartsOf L d
      if face.isEmpty then none else some (.darts face)

inductive Feature where
  | node (kind : NodeQuantity) (address : Address)
  | dart (kind : DartQuantity) (address : Address)
  | face (kind : FaceQuantity) (address : Address)
  | sumNodes (kind : NodeQuantity) (address : Address)
  | sumDarts (kind : DartQuantity) (address : Address)
  deriving DecidableEq, Repr

/-- Expand sums into actual variable addresses. Type mismatches are failures. -/
def Feature.instantiate (L : FaceList) (index : IndexValue) : Feature → Option (List Variable)
  | .node kind a => do
      let .node v ← a.eval L index | none
      return [.node kind v]
  | .dart kind a => do
      let .dart d ← a.eval L index | none
      return [.dart kind d]
  | .face kind a => do
      let .darts ds ← a.eval L index | none
      return [.face kind ds]
  | .sumNodes kind a => do
      let .nodes vs ← a.eval L index | none
      return vs.map (.node kind)
  | .sumDarts kind a => do
      let .darts ds ← a.eval L index | none
      return ds.map (.dart kind)

/-- A fixed integer row after the source's outward approximation. -/
structure RowTemplate where
  name : String
  standardOnly : Bool
  precision : ℕ
  pool : IndexPool
  terms : List (ℤ × Feature)
  rhs : ℤ

structure AffineRow where
  terms : List (ℚ × Variable)
  rhs : ℚ

def RowTemplate.instantiate (row : RowTemplate) (L : FaceList) (i : ℕ) : Option AffineRow := do
  let index ← (row.pool.values L)[i]?
  let terms ← row.terms.mapM (fun (c, feature) => do
    let coords ← feature.instantiate L index
    return coords.map (fun v => ((c : ℚ), v)))
  return ⟨terms.flatten, row.rhs⟩

end KeplerMission.SourceLP



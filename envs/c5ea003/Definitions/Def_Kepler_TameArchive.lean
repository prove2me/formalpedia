-- Prove2me | Definitions.Def_Kepler_TameArchive
-- name    : Kepler_TameArchive
-- status  : Definition
-- author  : @Minghui
-- created : 2026-09-27T02:52:57.836734+00:00
-- url     : https://prove2.me/theorems/adeb16af-e9d6-4ba3-b274-f6d11ff8cd5c
-- title:
--   Finite hypermaps, tameness and the fixed archive
-- statement:
--   A finite hypermap $H$ consists of a natural number $d$, darts $\{0,\ldots,d-1\}$ and permutations $e,n,f$ with $e(n(f(a)))=a$ for every dart. Let $E_a,N_a,F_a$ be its edge, node and face permutation-cycle orbits, including $a$, and let $\mathcal E,\mathcal N,\mathcal F$ be the finite sets of distinct such orbits. Let $\mathcal K$ be the finite set of distinct components reachable by zero or more applications of $e,n,f$. Incident faces at $a$ are the distinct sets $\mathcal I_a=\{F_b:b\in N_a\}$. Write $\mathcal T_a,\mathcal Q_a,\mathcal X_a$ for those incident faces of size $3$, size $4$, and size at least $5$, respectively, and $(p_a,q_a,x_a)=(|\mathcal T_a|,|\mathcal Q_a|,|\mathcal X_a|)$. The condition called tame requires $e^2=\mathrm{id}$; $|\mathcal N|+|\mathcal E|+|\mathcal F|=d+2|\mathcal K|$; $|\mathcal K|=1$; $N_a\cap F_a=\{a\}$ for every dart; $e(a)\neq a$; $b\in E_a\cap N_a\Rightarrow b=a$; $b\in N_a$ and $e(b)\in N_{e(a)}\Rightarrow b=a$; at least three distinct faces; $3\leq|F_a|\leq6$ and $3\leq|N_a|\leq7$ for every dart; $|\mathcal N|\in\{13,14,15\}$; and, whenever $|F_a|\geq5$, both $|N_a|\leq6$ and $|N_a|=6\Rightarrow(p_a,q_a,x_a)=(5,0,1)$. It further requires a real function $W$ on all finite subsets of the dart set with $W(F_a)\geq a_{|F_a|}$ for every dart, $\sum_{F\in\mathcal I_a}W(F)\geq b_{p_a,q_a}$ when $x_a=0$, $\sum_{F\in\mathcal T_a}W(F)\geq63/100$ when $(p_a,q_a,x_a)=(5,0,1)$, and $\sum_{F\in\mathcal F}W(F)<1541/1000$. The face constants are $a_3=0,a_4=206/1000,a_5=4819/10000,a_6=712/1000$, with $a_k=1541/1000$ otherwise. In the order $(p,q)=(0,3),(0,4),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1),(6,0),(7,0)$, the exceptional values of $b_{p,q}$ are $618/1000,97/100,656/1000,618/1000,797/1000,412/1000,12851/10000,311/1000,817/1000,347/1000,366/1000,4/100,1136/1000,686/1000,145/100$; every other pair has value $1541/1000$. Values of $W$ away from actual faces are unrestricted. An empty hypermap is a permitted structure but cannot be tame. A face list $L$ is a finite ordered list of finite lists of natural labels. A face $[v_0,\ldots,v_{k-1}]$ supplies the cyclic directed pairs $(v_i,v_{i+1\bmod k})$; an empty face supplies none, and a singleton supplies a loop. The dart list concatenates these lists with multiplicities. Good means no repeated directed pair, every face nonempty, and each occurring $(u,v)$ accompanied by $(v,u)$; it imposes no further length, label-range, connectedness or planarity condition, and the empty list is Good. The list represents $H$ if $e^2=\mathrm{id}$ and there exists a labeling $\ell$ of darts by natural numbers such that $\ell(a)=\ell(b)\Leftrightarrow b\in N_a$, the map $a\mapsto(\ell(a),\ell(f(a)))$ is injective, $(\ell(e(a)),\ell(f(e(a))))=(\ell(f(a)),\ell(a))$, every face of $L$ is a cyclic rotation of $[\ell(a),\ell(f(a)),\ldots,\ell(f^{|F_a|-1}(a))]$ for some dart $a$, and every dart has such a face in $L$. Representation alone permits repeating a face. The opposite hypermap has the same darts and permutations $f\circ n,n^{-1},f^{-1}$. The fixed archive has $19{,}715$ strings; decoding splits at periods into nonempty faces and maps A through O to labels $0$ through $14$. Empty strings, empty faces and other characters fail. Membership means equality to the decoded face list at some in-range index. Archive well-formedness requires successful decoding and Good at every index. A hypermap isomorphism is a bijection of dart sets commuting with all three permutations. The classification proposition is the following conjunction: Archive well-formedness holds, and every finite hypermap satisfying all the tame conditions has at least one archived face list representing it or its opposite. There is no claim that every archive entry is tame, no uniqueness assertion, and no nonlinear-catalogue premise. The assertion of successful decoding and Good at every archive index is unconditional even if no hypermap satisfied the tame hypotheses.
--
--   **Source and scope.** Primary §§7–8, pp.17–21; Blueprint WTEMDTA Theorem8.38; exact tame/tame_defs.hl, tame/tame_defs2.hl, formal_graph/archive/archive_all.ml. All 19,715 accompanying entries are included.
-- source:
--   Hales et al. (2017), A Formal Proof of the Kepler Conjecture, https://doi.org/10.1017/fmp.2017.1; Primary §§7–8, pp.17–21; Blueprint WTEMDTA Theorem8.38; exact tame/tame_defs.hl, tame/tame_defs2.hl, formal_graph/archive/archive_all.ml. All 19,715 accompanying entries are included.; https://github.com/flyspeck/flyspeck/tree/1ce0353008eba83d3c76ae9a25c3c242e4802d53

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
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Relation
import Mathlib.Data.List.Rotate
import Definitions.Def_Kepler_ArchiveData00
import Definitions.Def_Kepler_ArchiveData01

/-!
Finite hypermaps and the geometric tameness predicate used by Flyspeck.

Source: Hales, Dense Sphere Packings, Chapter 4, definitions ZIHYYRA and GUDUERI;
Chapter 8, definitions OOVCYPI, BTDOPPJ, DUSOAYQ and YOHGLNA. Exact formal source:
flyspeck/flyspeck@1ce0353008eba83d3c76ae9a25c3c242e4802d53,
text_formalization/hypermap/hypermap.hl and tame/tame_defs.hl:25–179.

The finite carrier is relabeled by `Fin`; no geometric property is encoded by this
representation. The real weight tables below are the HOL geometric tables, not
the slightly weakened integer tables used in the Isabelle enumeration.
-/

set_option autoImplicit false
open scoped BigOperators

namespace KeplerMission

/-- A finite dart set with edge, node and face permutations satisfying `e ∘ n ∘ f = id`. -/
structure FiniteHypermap where
  dartCount : ℕ
  edge : Equiv.Perm (Fin dartCount)
  node : Equiv.Perm (Fin dartCount)
  face : Equiv.Perm (Fin dartCount)
  coherence : ∀ d, edge (node (face d)) = d

namespace FiniteHypermap

/-- Orbit including fixed points, unlike the support of a nontrivial permutation cycle. -/
noncomputable def orbit {n : ℕ} (p : Equiv.Perm (Fin n)) (d : Fin n) : Finset (Fin n) :=
  @Finset.filter _ (fun x ↦ p.SameCycle d x) (Classical.decPred _) Finset.univ

noncomputable def edgeOrbit (H : FiniteHypermap) (d : Fin H.dartCount) := orbit H.edge d
noncomputable def nodeOrbit (H : FiniteHypermap) (d : Fin H.dartCount) := orbit H.node d
noncomputable def faceOrbit (H : FiniteHypermap) (d : Fin H.dartCount) := orbit H.face d

noncomputable def edgeSet (H : FiniteHypermap) : Finset (Finset (Fin H.dartCount)) :=
  Finset.univ.image H.edgeOrbit
noncomputable def nodeSet (H : FiniteHypermap) : Finset (Finset (Fin H.dartCount)) :=
  Finset.univ.image H.nodeOrbit
noncomputable def faceSet (H : FiniteHypermap) : Finset (Finset (Fin H.dartCount)) :=
  Finset.univ.image H.faceOrbit

def OneStep (H : FiniteHypermap) (d e : Fin H.dartCount) : Prop :=
  e = H.edge d ∨ e = H.node d ∨ e = H.face d

noncomputable def component (H : FiniteHypermap) (d : Fin H.dartCount) :=
  @Finset.filter _ (fun e ↦ Relation.ReflTransGen H.OneStep d e)
    (Classical.decPred _) Finset.univ

noncomputable def componentSet (H : FiniteHypermap) : Finset (Finset (Fin H.dartCount)) :=
  Finset.univ.image H.component

def IsPlain (H : FiniteHypermap) : Prop := ∀ d, H.edge (H.edge d) = d

/-- Euler characteristic, with the number of connected components, exactly as in HOL. -/
def IsPlanar (H : FiniteHypermap) : Prop :=
  H.nodeSet.card + H.edgeSet.card + H.faceSet.card = H.dartCount + 2 * H.componentSet.card

def IsConnected (H : FiniteHypermap) : Prop := H.componentSet.card = 1

def IsSimple (H : FiniteHypermap) : Prop :=
  ∀ d, H.nodeOrbit d ∩ H.faceOrbit d = {d}

def IsEdgeNondegenerate (H : FiniteHypermap) : Prop := ∀ d, H.edge d ≠ d

def HasNoLoops (H : FiniteHypermap) : Prop :=
  ∀ d e, e ∈ H.edgeOrbit d → e ∈ H.nodeOrbit d → e = d

def HasNoDoubleJoins (H : FiniteHypermap) : Prop :=
  ∀ d e, e ∈ H.nodeOrbit d → H.edge e ∈ H.nodeOrbit (H.edge d) → e = d

noncomputable def incidentFaces (H : FiniteHypermap) (d : Fin H.dartCount) :=
  (H.nodeOrbit d).image H.faceOrbit

noncomputable def trianglesAt (H : FiniteHypermap) (d : Fin H.dartCount) :=
  (H.incidentFaces d).filter (fun F ↦ F.card = 3)

noncomputable def quadrilateralsAt (H : FiniteHypermap) (d : Fin H.dartCount) :=
  (H.incidentFaces d).filter (fun F ↦ F.card = 4)

noncomputable def exceptionalFacesAt (H : FiniteHypermap) (d : Fin H.dartCount) :=
  (H.incidentFaces d).filter (fun F ↦ 5 ≤ F.card)

noncomputable def nodeType (H : FiniteHypermap) (d : Fin H.dartCount) : ℕ × ℕ × ℕ :=
  ((H.trianglesAt d).card, (H.quadrilateralsAt d).card, (H.exceptionalFacesAt d).card)

/-- The exact HOL geometric `b_tame` table, in rational notation. -/
def tameVertexWeight (p q : ℕ) : ℚ :=
  match p, q with
  | 0, 3 => 618 / 1000
  | 0, 4 => 97 / 100
  | 1, 2 => 656 / 1000
  | 1, 3 => 618 / 1000
  | 2, 1 => 797 / 1000
  | 2, 2 => 412 / 1000
  | 2, 3 => 12851 / 10000
  | 3, 1 => 311 / 1000
  | 3, 2 => 817 / 1000
  | 4, 0 => 347 / 1000
  | 4, 1 => 366 / 1000
  | 5, 0 => 4 / 100
  | 5, 1 => 1136 / 1000
  | 6, 0 => 686 / 1000
  | 7, 0 => 145 / 100
  | _, _ => 1541 / 1000

/-- The HOL `d_tame` table; the distinction for n<3 is irrelevant under tameness. -/
def tameFaceWeight (n : ℕ) : ℚ :=
  match n with
  | 3 => 0
  | 4 => 206 / 1000
  | 5 => 4819 / 10000
  | 6 => 712 / 1000
  | _ => 1541 / 1000

def AdmissibleWeight (H : FiniteHypermap) (w : Finset (Fin H.dartCount) → ℝ) : Prop :=
  (∀ d, (tameFaceWeight (H.faceOrbit d).card : ℝ) ≤ w (H.faceOrbit d)) ∧
  (∀ d, (H.exceptionalFacesAt d).card = 0 →
    (tameVertexWeight (H.trianglesAt d).card (H.quadrilateralsAt d).card : ℝ) ≤
      ∑ F ∈ H.incidentFaces d, w F) ∧
  (∀ d, H.nodeType d = (5, 0, 1) → (63 : ℝ) / 100 ≤ ∑ F ∈ H.trianglesAt d, w F)

/-- Exact `tame_planar_hypermap` from `tame_defs.hl`, with its real weight table. -/
def IsTame (H : FiniteHypermap) : Prop :=
  H.IsPlain ∧ H.IsPlanar ∧ H.IsConnected ∧ H.IsSimple ∧ H.IsEdgeNondegenerate ∧
  H.HasNoLoops ∧ H.HasNoDoubleJoins ∧ 3 ≤ H.faceSet.card ∧
  (∀ d, 3 ≤ (H.faceOrbit d).card ∧ (H.faceOrbit d).card ≤ 6) ∧
  (H.nodeSet.card = 13 ∨ H.nodeSet.card = 14 ∨ H.nodeSet.card = 15) ∧
  (∀ d, 3 ≤ (H.nodeOrbit d).card ∧ (H.nodeOrbit d).card ≤ 7) ∧
  (∀ d, 5 ≤ (H.faceOrbit d).card →
    ((H.nodeOrbit d).card = 6 → H.nodeType d = (5, 0, 1)) ∧
    (H.nodeOrbit d).card ≤ 6) ∧
  ∃ w : Finset (Fin H.dartCount) → ℝ,
    H.AdmissibleWeight w ∧ (∑ F ∈ H.faceSet, w F) < (1541 : ℝ) / 1000

/-- Reverse orientation: `(f ∘ n, n⁻¹, f⁻¹)`, not merely inversion of the edge map. -/
def opposite (H : FiniteHypermap) : FiniteHypermap where
  dartCount := H.dartCount
  edge := H.node.trans H.face
  node := H.node.symm
  face := H.face.symm
  coherence := by intro d; simp

end FiniteHypermap

/-- A dart bijection intertwining each of the three hypermap permutations. -/
structure HypermapIso (H K : FiniteHypermap) where
  dartEquiv : Fin H.dartCount ≃ Fin K.dartCount
  edge_comm : ∀ d, dartEquiv (H.edge d) = K.edge (dartEquiv d)
  node_comm : ∀ d, dartEquiv (H.node d) = K.node (dartEquiv d)
  face_comm : ∀ d, dartEquiv (H.face d) = K.face (dartEquiv d)

end KeplerMission


/-!
Exact accompanying Flyspeck archive, ordinary immutable specification data.
Source: flyspeck/flyspeck@1ce0353008eba83d3c76ae9a25c3c242e4802d53,
formal_graph/archive/archive_all.ml, SHA256
703ea865a124aa69f0ee12d94df7065bbbf5701a3085776e24632d14493474db.
The four AFP archive lists are identical, in order: Tri9, Quad1253, Pent16080,
Hex2373. These 19715 rows also occur at the 2014 submitted-version revision.
The overview paper section7.3 reports18762; that count differs from the concrete
accompanying data. No theorem here assumes either number as a mathematical premise.
Each uppercase letter A..O encodes one vertex0..14; dots separate face cycles.
The decoder returns Option and the contract requires every row to decode and be good.
No external result, hash or generator output is used as proof of classification.
-/
set_option autoImplicit false
set_option maxRecDepth 4096

namespace KeplerMission

abbrev FaceList := List (List ℕ)

namespace FaceList

def faceDarts (f : List ℕ) : List (ℕ × ℕ) := f.zip (f.rotate 1)

def darts (L : FaceList) : List (ℕ × ℕ) := L.flatMap faceDarts

/-- The exact source good_list conditions, without treating wellformedness as automatic. -/
def Good (L : FaceList) : Prop :=
  L.darts.Nodup ∧ (∀ f ∈ L, f ≠ []) ∧
    ∀ a b, (a, b) ∈ L.darts → (b, a) ∈ L.darts

/-- A cyclic list visits a face once, following the face permutation. -/
noncomputable def faceListing (H : FiniteHypermap) (label : Fin H.dartCount → ℕ)
    (d : Fin H.dartCount) : List ℕ :=
  (List.range (H.faceOrbit d).card).map (fun i ↦ label ((H.face ^ i) d))

/-- Exact node labels and complete face cycles, up to the choice of first vertex. -/
def Represents (L : FaceList) (H : FiniteHypermap) : Prop :=
  H.IsPlain ∧ ∃ label : Fin H.dartCount → ℕ,
    (∀ d e, label d = label e ↔ e ∈ H.nodeOrbit d) ∧
    Function.Injective (fun d ↦ (label d, label (H.face d))) ∧
    (∀ d, (label (H.edge d), label (H.face (H.edge d))) = (label (H.face d), label d)) ∧
    (∀ f ∈ L, ∃ d, List.IsRotated (faceListing H label d) f) ∧
    (∀ d, ∃ f ∈ L, List.IsRotated (faceListing H label d) f)

end FaceList

namespace ArchiveEncoding

def decodeVertex (c : Char) : Option ℕ :=
  if 'A' ≤ c ∧ c ≤ 'O' then some (c.toNat - 'A'.toNat) else none

def decodeFace (s : String) : Option (List ℕ) :=
  if s.isEmpty then none else s.toList.mapM decodeVertex

def decode (s : String) : Option FaceList :=
  if s.isEmpty then none else (s.splitOn ".").mapM decodeFace

def codes : Array String :=
  archiveDataBlock0 ++ archiveDataBlock1

end ArchiveEncoding

/-- Every archive row remains represented, including potential decoding failures. -/
def tameArchiveEntries : Array (Option FaceList) :=
  ArchiveEncoding.codes.map ArchiveEncoding.decode

/-- Membership in the concrete accompanying archive, not in a set selected by tameness. -/
def InTameArchive (L : FaceList) : Prop :=
  ∃ i : Fin tameArchiveEntries.size, tameArchiveEntries[i] = some L

/-- No malformed data may be ignored: every actual row must decode to a good list. -/
def ArchiveWellFormed : Prop :=
  ∀ i : Fin tameArchiveEntries.size, ∃ L, tameArchiveEntries[i] = some L ∧ L.Good

/-- Source-backed classification obligation including the hypermap/plane-graph bridge.
Hales et al.2017 sections7–8; Blueprint Theorem8.38 WTEMDTA. This is an unproved
proposition type, not an assertion of the classification result. -/
def TameArchiveClassification : Prop :=
  ArchiveWellFormed ∧ ∀ H : FiniteHypermap, H.IsTame →
    ∃ L : FaceList, InTameArchive L ∧ (L.Represents H ∨ L.Represents H.opposite)

end KeplerMission



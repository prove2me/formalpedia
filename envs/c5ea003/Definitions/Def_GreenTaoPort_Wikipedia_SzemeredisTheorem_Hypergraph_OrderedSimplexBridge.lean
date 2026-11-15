-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedSimplexBridge
-- name    : GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedSimplexBridge
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T08:59:37.314002+00:00
-- url     : https://prove2.me/theorems/8da2fb1b-9d47-4117-aab0-0be6a46006c9
-- title:
--   Identifying simplex colours with ordered facets
-- statement:
--   In an $(n+1)$-partite simplex, colour $j$ corresponds to the increasing rank-$n$ face omitting coordinate $j$. This is an equivalence between colours and ordered facets. Each dependent deleted-vector space is explicitly equivalent to the ordinary $n$-tuple space.
--
--   For a simplex hypergraph with the same vertex type in every part, these reindexings produce a complete ordered pattern: decode an ordered facet by its omitted colour and apply that colour's edge predicate. An ordered deletion family is transported back to the simplex's dependent face spaces by the same canonical coordinate conversion.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/OrderedSimplexBridge.lean#L19-L196

import Mathlib.Order.Hom.PowersetCard
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_APRemoval
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedPattern
import Lean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Equal-vertex bridge from ordered removal to simplex removal

For `n + 1` equal vertex classes, the colours of a partite `n`-uniform
simplex hypergraph are canonically the increasing `n`-faces of
`Fin (n + 1)`: the colour `j` corresponds to the face which omits `j`.
This file makes that identification explicit and transports occurrences,
deletion covers, and normalized deletion cost.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- The colour `j` regarded as the increasing codimension-one face which
omits `j`. -/
def orderedFacet {n : ℕ} (j : Fin (n + 1)) :
    OrderedFace (n + 1) n :=
  Fin.succAboveOrderEmb j

/-- Colours of an `(n + 1)`-vertex simplex are equivalent to increasing
rank-`n` faces.  The construction factors through finite subsets so that its
forward map is definitionally the complement of a singleton. -/
noncomputable def orderedFacetEquiv (n : ℕ) :
    Fin (n + 1) ≃ OrderedFace (n + 1) n :=
  (Set.powersetCard.ofSingleton :
      Fin (n + 1) ≃ Set.powersetCard (Fin (n + 1)) 1) |>.trans
    ((Set.powersetCard.compl (m := n) (n := 1) (by simp) :
        Set.powersetCard (Fin (n + 1)) 1 ≃
          Set.powersetCard (Fin (n + 1)) n) |>.trans
      (Set.powersetCard.ofFinEmbEquiv :
        OrderedFace (n + 1) n ≃
          Set.powersetCard (Fin (n + 1)) n).symm)



/-- The two standard presentations of a deleted coordinate vector are
mutually inverse. -/
@[simp]
theorem deletedVectorToFinTuple_finTupleToDeletedVector
    {G : Type*} {n : ℕ} (j : Fin (n + 1))
    (y : Fin n → G) :
    deletedVectorToFinTuple j
        (finTupleToDeletedVector j y) = y := by
  funext t
  simp [deletedVectorToFinTuple]

@[simp]
theorem finTupleToDeletedVector_deletedVectorToFinTuple
    {G : Type*} {n : ℕ} (j : Fin (n + 1))
    (x : DeletedVector (fun _ : Fin (n + 1) => G) j) :
    finTupleToDeletedVector j
        (deletedVectorToFinTuple j x) = x := by
  funext i
  change
    x (finSuccAboveEquiv j
        ((finSuccAboveEquiv j).symm i)) = x i
  rw [(finSuccAboveEquiv j).apply_symm_apply]

/-- Reindexing identifies the deleted-vector space of every colour with the
same ordinary tuple space. -/
noncomputable def deletedVectorFinTupleEquiv
    {G : Type*} {n : ℕ} (j : Fin (n + 1)) :
    DeletedVector (fun _ : Fin (n + 1) => G) j ≃
      (Fin n → G) where
  toFun := deletedVectorToFinTuple j
  invFun := finTupleToDeletedVector j
  left_inv := finTupleToDeletedVector_deletedVectorToFinTuple j
  right_inv := deletedVectorToFinTuple_finTupleToDeletedVector j





/-- Regard an equal-vertex simplex hypergraph as a complete ordered pattern.
An arbitrary ordered face is first decoded as its unique omitted colour. -/
noncomputable def SimplexHypergraph.toOrderedPattern
    {G : Type*} {n : ℕ}
    (H : SimplexHypergraph (fun _ : Fin (n + 1) => G)) :
    OrderedPattern G (n + 1) n where
  edge e y :=
    let j := (orderedFacetEquiv n).symm e
    H.edge j (finTupleToDeletedVector j y)









/-- Send an ordered deletion on the face omitting `j` to the corresponding
dependent deleted-vector space. -/
noncomputable def orderedDeletionToSimplex
    {G : Type*} [DecidableEq G] {n : ℕ}
    (D : OrderedPattern.DeletionFamily
      (G := G) (n + 1) n) :
    SimplexHypergraph.DeletionFamily
      (fun _ : Fin (n + 1) => G) := by
  classical
  exact fun j =>
    (D (orderedFacet j)).image
      (finTupleToDeletedVector j)















end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.orderedDeletionToSimplex.eq_1,
    `Wikipedia.SzemeredisTheorem.orderedFacetEquiv.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"



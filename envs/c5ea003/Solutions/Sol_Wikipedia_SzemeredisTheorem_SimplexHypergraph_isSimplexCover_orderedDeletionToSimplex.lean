-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.SimplexHypergraph.isSimplexCover_orderedDeletionToSimplex
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:41:18.95221+00:00
-- url     : https://prove2.me/submissions/9e5a837e-a855-4db5-9bf5-137b1eb334f2

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_APCorrespondence
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_APRemoval
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_ConditionalAverage
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Energy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_FacePartition
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedPattern
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedSimplexBridge
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Removal
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Simplex
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Unweighted
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_LinearForms_Basic
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Szemeredi_Weighted
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_APCut
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutDiscrepancy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutTransport
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
import Mathlib.Order.Hom.PowersetCard
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SimplexHypergraph_toOrderedPattern_isOccurrence_iff
import Theorems.Thm_Wikipedia_SzemeredisTheorem_orderedFacetEquiv_apply

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section


/-!
# Complete ordered partite hypergraph patterns

Recursive hypergraph removal naturally produces lower-rank constraints on a
fixed collection of vertex classes.  It is convenient to index an ordered
rank-`r` face by an embedding `Fin r ↪ Fin k`.  This permits composition of
faces without quotienting by permutations.

This file defines weighted and unweighted complete ordered patterns, their
normalized occurrence counts, deletions, and the uniform removal property
used by the rank induction.  Rank zero is proved directly.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

































namespace WeightedOrderedPattern











end WeightedOrderedPattern



namespace OrderedPattern





@[simp]
theorem mem_occurrenceFinset
    {G : Type*} [Fintype G] [DecidableEq G] {k r : ℕ}
    (H : OrderedPattern G k r)
    (x : Fin k → G) :
    x ∈ H.occurrenceFinset ↔ H.IsOccurrence x := by
  simp [occurrenceFinset]

























end OrderedPattern







end Wikipedia.SzemeredisTheorem

end

section






/-!
# Arithmetic-progression face forms as transported cut forms

For a fixed deleted vertex, the arithmetic-progression face form has
coefficients `i - j`.  Coprimality of the modulus with `(k-1)!` makes every
one of these coefficients a unit, so the face form is an automorphic
coordinate sum.  This file proves the coefficient and reindexing facts needed
to apply transported cut discrepancy.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators









@[simp]
theorem finSuccAboveEquiv_apply_val
    {n : ℕ} (j : Fin (n + 1)) (t : Fin n) :
    (finSuccAboveEquiv j t).1 = j.succAbove t :=
  rfl















end Wikipedia.SzemeredisTheorem

end

section




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













@[simp]
theorem deletedVectorToFinTuple_deleteCoordinate_eq_orderedFaceTuple
    {G : Type*} {n : ℕ} (j : Fin (n + 1))
    (x : Fin (n + 1) → G) :
    deletedVectorToFinTuple j (deleteCoordinate x j) =
      orderedFaceTuple (orderedFacet j) x := by
  rfl









/-- The finite occurrence set is unchanged by the ordered presentation. -/
theorem SimplexHypergraph.toOrderedPattern_occurrenceFinset
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (H : SimplexHypergraph (fun _ : Fin (n + 1) => G)) :
    H.toOrderedPattern.occurrenceFinset =
      H.simplexFinset := by
  ext x
  rw [OrderedPattern.mem_occurrenceFinset,
    SimplexHypergraph.mem_simplexFinset,
    H.toOrderedPattern_isOccurrence_iff]





@[simp]
theorem mem_orderedDeletionToSimplex_iff
    {G : Type*} [DecidableEq G] {n : ℕ}
    (D : OrderedPattern.DeletionFamily
      (G := G) (n + 1) n)
    (j : Fin (n + 1))
    (x : DeletedVector (fun _ : Fin (n + 1) => G) j) :
    x ∈ orderedDeletionToSimplex D j ↔
      deletedVectorToFinTuple j x ∈ D (orderedFacet j) := by
  classical
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hx
    rw [← hyx]
    simpa using hy
  · intro hx
    exact Finset.mem_image.mpr
      ⟨deletedVectorToFinTuple j x, hx,
        finTupleToDeletedVector_deletedVectorToFinTuple j x⟩













end Wikipedia.SzemeredisTheorem

end
/-!
# Equal-vertex bridge from ordered removal to simplex removal

For `n + 1` equal vertex classes, the colours of a partite `n`-uniform
simplex hypergraph are canonically the increasing `n`-faces of
`Fin (n + 1)`: the colour `j` corresponds to the face which omits `j`.
This file makes that identification explicit and transports occurrences,
deletion covers, and normalized deletion cost.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators

open Wikipedia.SzemeredisTheorem.SimplexHypergraph in
/-- A cover of the ordered presentation transports to a simplex cover. -/
theorem solution
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (H : SimplexHypergraph (fun _ : Fin (n + 1) => G))
    (D : OrderedPattern.DeletionFamily
      (G := G) (n + 1) n)
    (hcover : H.toOrderedPattern.IsCover D) :
    H.IsSimplexCover (orderedDeletionToSimplex D) := by
  intro x hx
  have hxOrdered :
      x ∈ H.toOrderedPattern.occurrenceFinset := by
    rw [H.toOrderedPattern_occurrenceFinset]
    exact hx
  obtain ⟨e, he⟩ := hcover x hxOrdered
  let j := (orderedFacetEquiv n).symm e
  have heq : orderedFacet j = e := by
    rw [← orderedFacetEquiv_apply]
    exact (orderedFacetEquiv n).apply_symm_apply e
  refine ⟨j, (mem_orderedDeletionToSimplex_iff D j _).2 ?_⟩
  rw [
    deletedVectorToFinTuple_deleteCoordinate_eq_orderedFaceTuple,
    heq]
  exact he

-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.SimplexHypergraph.toOrderedPattern_isOccurrence_iff
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:33:12.780084+00:00
-- url     : https://prove2.me/submissions/2ae3ea66-7d91-4f43-827b-397b3ff3bd99

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_orderedFacetEquiv_apply

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

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
theorem finTupleToDeletedVector_orderedFaceTuple
    {G : Type*} {n : ℕ} (j : Fin (n + 1))
    (x : Fin (n + 1) → G) :
    finTupleToDeletedVector j
        (orderedFaceTuple (orderedFacet j) x) =
      deleteCoordinate x j := by
  rw [←
    finTupleToDeletedVector_deletedVectorToFinTuple j
      (deleteCoordinate x j)]
  congr



@[simp]
theorem SimplexHypergraph.toOrderedPattern_edge_orderedFacet
    {G : Type*} {n : ℕ}
    (H : SimplexHypergraph (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1)) (y : Fin n → G) :
    H.toOrderedPattern.edge (orderedFacet j) y ↔
      H.edge j (finTupleToDeletedVector j y) := by
  change
    H.edge ((orderedFacetEquiv n).symm (orderedFacet j))
        (finTupleToDeletedVector
          ((orderedFacetEquiv n).symm (orderedFacet j)) y) ↔
      H.edge j (finTupleToDeletedVector j y)
  have hj :
      (orderedFacetEquiv n).symm (orderedFacet j) = j := by
    rw [← orderedFacetEquiv_apply]
    exact (orderedFacetEquiv n).symm_apply_apply j
  rw [hj]























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
/-- Ordered occurrences are exactly labelled simplices. -/
theorem solution
    {G : Type*} {n : ℕ}
    (H : SimplexHypergraph (fun _ : Fin (n + 1) => G))
    (x : Fin (n + 1) → G) :
    H.toOrderedPattern.IsOccurrence x ↔
      ∀ j, H.edge j (deleteCoordinate x j) := by
  constructor
  · intro hx j
    have hj := hx (orderedFacet j)
    rw [H.toOrderedPattern_edge_orderedFacet] at hj
    simpa using hj
  · intro hx e
    let j := (orderedFacetEquiv n).symm e
    have he : orderedFacet j = e := by
      rw [← orderedFacetEquiv_apply]
      exact (orderedFacetEquiv n).apply_symm_apply e
    rw [← he]
    rw [H.toOrderedPattern_edge_orderedFacet]
    simpa using hx j

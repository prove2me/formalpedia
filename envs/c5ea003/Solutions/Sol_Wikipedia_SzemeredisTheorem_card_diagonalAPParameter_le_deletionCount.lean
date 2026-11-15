-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.card_diagonalAPParameter_le_deletionCount
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:35:31.303171+00:00
-- url     : https://prove2.me/submissions/e8b23f1e-9a20-4649-809e-116291fa3552

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_APCorrespondence
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_APRemoval
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_ConditionalAverage
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Energy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_FacePartition
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
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SimplexHypergraph_card_deletionSlotFinset_le_deletionCount
import Theorems.Thm_Wikipedia_SzemeredisTheorem_diagonalCoveredSlot_injective

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
# From partite simplex removal to dense arithmetic progressions

For a finite set `A ⊆ ZMod N`, its arithmetic-progression hypergraph has
one edge of colour `j` whenever the `j`th AP form belongs to `A`.  The
degenerate progressions of common difference zero give a large,
edge-disjoint family of labelled simplices.  Consequently every simplex
cover has normalized deletion cost at least `mean (1_A) / k`.

This is the elementary half of the standard deduction of dense
Szemerédi from the partite simplex-removal lemma.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators





























namespace SimplexHypergraph



theorem mem_deletionSlotFinset
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (deleted :
      DeletionFamily (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1))
    (x : DeletedVector (fun _ : Fin (n + 1) => G) j)
    (hx : x ∈ deleted j) :
    (j, deletedVectorToFinTuple j x) ∈
      deletionSlotFinset deleted := by
  classical
  apply Finset.mem_biUnion.mpr
  refine ⟨j, Finset.mem_univ j, ?_⟩
  exact Finset.mem_image.mpr ⟨x, hx, rfl⟩



end SimplexHypergraph



@[simp]
theorem diagonalCoverColor_mem
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N))
    (deleted :
      SimplexHypergraph.DeletionFamily
        (fun _ : Fin (r + 2) => ZMod N))
    (hcover :
      (apSetHypergraph (r + 2) N A).IsSimplexCover deleted)
    (p : DiagonalAPParameter r N A) :
    deleteCoordinate (diagonalAPSimplex r N A p)
        (diagonalCoverColor r N A deleted hcover p) ∈
      deleted (diagonalCoverColor r N A deleted hcover p) :=
  Classical.choose_spec
    (hcover (diagonalAPSimplex r N A p)
      (diagonalAPSimplex_mem_simplexFinset r N A p))



theorem diagonalCoveredSlot_mem_deletionSlotFinset
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N))
    (deleted :
      SimplexHypergraph.DeletionFamily
        (fun _ : Fin (r + 2) => ZMod N))
    (hcover :
      (apSetHypergraph (r + 2) N A).IsSimplexCover deleted)
    (p : DiagonalAPParameter r N A) :
    diagonalCoveredSlot r N A deleted hcover p ∈
      SimplexHypergraph.deletionSlotFinset deleted := by
  classical
  exact SimplexHypergraph.mem_deletionSlotFinset deleted
    (diagonalCoverColor r N A deleted hcover p)
    (deleteCoordinate (diagonalAPSimplex r N A p)
      (diagonalCoverColor r N A deleted hcover p))
    (diagonalCoverColor_mem r N A deleted hcover p)

















end Wikipedia.SzemeredisTheorem

end
/-!
# From partite simplex removal to dense arithmetic progressions

For a finite set `A ⊆ ZMod N`, its arithmetic-progression hypergraph has
one edge of colour `j` whenever the `j`th AP form belongs to `A`.  The
degenerate progressions of common difference zero give a large,
edge-disjoint family of labelled simplices.  Consequently every simplex
cover has normalized deletion cost at least `mean (1_A) / k`.

This is the elementary half of the standard deduction of dense
Szemerédi from the partite simplex-removal lemma.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators

open Wikipedia.SzemeredisTheorem in
/-- Every cover of the AP-set hypergraph deletes at least one distinct face
for each member of the degenerate simplex family. -/
theorem solution
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N))
    (deleted :
      SimplexHypergraph.DeletionFamily
        (fun _ : Fin (r + 2) => ZMod N))
    (hcover :
      (apSetHypergraph (r + 2) N A).IsSimplexCover deleted) :
    Fintype.card (DiagonalAPParameter r N A) ≤
      SimplexHypergraph.deletionCount deleted := by
  classical
  let f := diagonalCoveredSlot r N A deleted hcover
  calc
    Fintype.card (DiagonalAPParameter r N A) =
        (Finset.univ.image f).card := by
      rw [Finset.card_image_of_injective _ 
        (diagonalCoveredSlot_injective r N A deleted hcover)]
      simp
    _ ≤
        (SimplexHypergraph.deletionSlotFinset deleted).card := by
      apply Finset.card_le_card
      intro y hy
      obtain ⟨p, _hp, rfl⟩ := Finset.mem_image.mp hy
      exact diagonalCoveredSlot_mem_deletionSlotFinset
        r N A deleted hcover p
    _ ≤ SimplexHypergraph.deletionCount deleted :=
      SimplexHypergraph.card_deletionSlotFinset_le_deletionCount
        deleted

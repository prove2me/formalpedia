-- Prove2me | solution 1 for BourgainSlicingConnector.exists_width_le_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T20:24:18.714031+00:00
-- url     : https://prove2.me/submissions/ade69074-eb88-48ad-9eee-2ceafd8f4b37

-- Sol generated from Shared/BourgainSlicingConnector/BourgainSlicingConnector.lean
import Mathlib
import Definitions.Def_Shared_BourgainSlicingConnector_BourgainSlicingConnector

/-!
# A finite multiplicative bridge for coordinate slices of unit-volume boxes

For an axis-aligned box with positive side lengths `a i`, its volume is the product
of the side lengths.  Its coordinate section perpendicular to axis `i` has volume
the product of all the other side lengths.  Thus the geometric slicing assertion for
boxes is exactly a finite multiplicative pigeonhole principle.

This is a rigorously proved special case and structural model of Bourgain's slicing
problem; it does not claim the open dimension-free theorem for arbitrary convex bodies.
-/

open BourgainSlicingConnector








open BourgainSlicingConnector in
theorem solution{n : ℕ} (hn : 0 < n) (a : Fin n → ℝ)
    (hvol : boxVolume a = 1) :
    ∃ i, a i ≤ 1 := by
  by_contra h
  push_neg at h
  rw [boxVolume] at hvol
  have hprod : ∏ i, a i > 1 := by
    have aux : ∀ m : ℕ, 0 < m → ∀ (f : Fin m → ℝ), (∀ i, 1 < f i) → ∏ i, f i > 1 := by
      intro m hm f hf
      induction hm with
      | refl => simp [hf 0]
      | step _ ih =>
        rw [Fin.prod_univ_succ]
        have h2 : 1 < ∏ i : Fin _, f i.succ := ih (fun i => f i.succ) (fun i => hf i.succ)
        exact one_lt_mul_of_lt_of_le (hf 0) h2.le
    exact aux n hn a h
  linarith

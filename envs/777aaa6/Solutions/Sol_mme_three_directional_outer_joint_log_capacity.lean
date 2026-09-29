-- Prove2me | solution 1 for mme_three_directional_outer_joint_log_capacity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-07T00:38:51.482987+00:00
-- url     : https://prove2.me/submissions/c37c1610-b0f8-4a8d-8a4f-a5a2862f413a

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

private theorem log_min_of_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.log (min x y) = min (Real.log x) (Real.log y) := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, min_eq_left (Real.log_le_log hx h)]
  · rw [min_eq_right h, min_eq_right (Real.log_le_log hy h)]

/-- Combine the three directional consumers before taking their minimum.
The lower-bound interface needs outer and joint rates, not a separate H rate. -/
theorem solution (A H : Fin 3 → ℝ)
    (hA : ∀ i, 0 < A i) (hH : ∀ i, 0 < H i) :
    Real.log ((A 0 * A 1 * A 2) *
        min (H 1 * H 2) (min (H 0 * H 2) (H 0 * H 1))) =
      min (Real.log (A 0) + Real.log (A 1 * H 1) + Real.log (A 2 * H 2))
        (min (Real.log (A 1) + Real.log (A 0 * H 0) + Real.log (A 2 * H 2))
          (Real.log (A 2) + Real.log (A 0 * H 0) + Real.log (A 1 * H 1))) ∧
    ∀ (a r : Fin 3 → ℝ),
      (∀ i, a i ≤ Real.log (A i)) →
      (∀ i, r i ≤ Real.log (A i * H i)) →
        min (a 0 + r 1 + r 2)
          (min (a 1 + r 0 + r 2) (a 2 + r 0 + r 1)) ≤
        Real.log ((A 0 * A 1 * A 2) *
          min (H 1 * H 2) (min (H 0 * H 2) (H 0 * H 1))) := by
  have hA01 : 0 < A 0 * A 1 := mul_pos (hA 0) (hA 1)
  have hAprod : 0 < A 0 * A 1 * A 2 := mul_pos hA01 (hA 2)
  have hH12 : 0 < H 1 * H 2 := mul_pos (hH 1) (hH 2)
  have hH02 : 0 < H 0 * H 2 := mul_pos (hH 0) (hH 2)
  have hH01 : 0 < H 0 * H 1 := mul_pos (hH 0) (hH 1)
  have hmin : 0 < min (H 1 * H 2) (min (H 0 * H 2) (H 0 * H 1)) :=
    lt_min hH12 (lt_min hH02 hH01)
  have hLA : Real.log (A 0 * A 1 * A 2) =
      Real.log (A 0) + Real.log (A 1) + Real.log (A 2) := by
    rw [Real.log_mul hA01.ne' (hA 2).ne', Real.log_mul (hA 0).ne' (hA 1).ne']
  have hLH (i j : Fin 3) : Real.log (H i * H j) = Real.log (H i) + Real.log (H j) :=
    Real.log_mul (hH i).ne' (hH j).ne'
  have hLAH (i : Fin 3) : Real.log (A i * H i) = Real.log (A i) + Real.log (H i) :=
    Real.log_mul (hA i).ne' (hH i).ne'
  have hid : Real.log ((A 0 * A 1 * A 2) *
        min (H 1 * H 2) (min (H 0 * H 2) (H 0 * H 1))) =
      min (Real.log (A 0) + Real.log (A 1 * H 1) + Real.log (A 2 * H 2))
        (min (Real.log (A 1) + Real.log (A 0 * H 0) + Real.log (A 2 * H 2))
          (Real.log (A 2) + Real.log (A 0 * H 0) + Real.log (A 1 * H 1))) := by
    rw [Real.log_mul hAprod.ne' hmin.ne', hLA,
      log_min_of_pos hH12 (lt_min hH02 hH01), log_min_of_pos hH02 hH01]
    simp only [hLH, hLAH, ← min_add_add_left]
    congr 1
    · ring
    · congr 1 <;> ring
  refine ⟨hid, ?_⟩
  intro a r ha hr
  rw [hid]
  exact min_le_min
    (add_le_add (add_le_add (ha 0) (hr 1)) (hr 2))
    (min_le_min
      (add_le_add (add_le_add (ha 1) (hr 0)) (hr 2))
      (add_le_add (add_le_add (ha 2) (hr 0)) (hr 1)))

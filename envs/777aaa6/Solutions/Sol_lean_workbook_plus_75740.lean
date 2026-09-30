-- Prove2me | solution 1 for lean_workbook_plus_75740
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:32:28.319557+00:00
-- url     : https://prove2.me/submissions/f560808b-7d17-4f6c-8c72-9555eeeb43ce

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

theorem quintic_quantitative_bound (x : ℝ) (hx : 3 ≤ x) :
    108 * (x - 3) ≤ x ^ 5 - 3 * x ^ 3 - 36 * x ^ 2 + 162 := by
  have ht : 0 ≤ x - 3 := by linarith
  have hid : x ^ 5 - 3 * x ^ 3 - 36 * x ^ 2 + 162 =
      (x - 3) ^ 5 + 15 * (x - 3) ^ 4 + 87 * (x - 3) ^ 3 +
        207 * (x - 3) ^ 2 + 108 * (x - 3) := by ring
  rw [hid]
  nlinarith [pow_nonneg ht 5, pow_nonneg ht 4, pow_nonneg ht 3, sq_nonneg (x - 3)]

theorem quintic_boundary_equality (x : ℝ) (hx : 3 ≤ x) :
    x ^ 5 - 3 * x ^ 3 - 36 * x ^ 2 + 162 = 0 ↔ x = 3 := by
  constructor
  · intro h
    have := quintic_quantitative_bound x hx
    linarith
  · rintro rfl
    norm_num

theorem solution (x : ℝ) (h : x ≥ 3) :
    x ^ 5 - 3 * x ^ 3 - 36 * x ^ 2 + 162 ≥ 0 := by
  have := quintic_quantitative_bound x h
  linarith

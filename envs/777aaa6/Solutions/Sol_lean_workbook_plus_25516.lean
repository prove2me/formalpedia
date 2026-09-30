-- Prove2me | solution 1 for lean_workbook_plus_25516
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:10:35.97026+00:00
-- url     : https://prove2.me/submissions/7e33cd99-ca2d-4766-b29a-f329c23ac19b

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

lemma nonnegative_lower_bound (x : ℝ) (hx : 0 ≤ x) :
    7 / 8 ≤ 4 * x ^ 6 - 3 * x ^ 5 + x ^ 4 + 5 * x ^ 3 + 2 * x ^ 2 - x + 1 := by
  have hq : 0 ≤ 4 * x ^ 2 - 3 * x + 1 := by nlinarith [sq_nonneg (8 * x - 3)]
  have hr : 7 / 8 ≤ 2 * x ^ 2 - x + 1 := by nlinarith [sq_nonneg (4 * x - 1)]
  nlinarith [mul_nonneg (pow_nonneg hx 4) hq, pow_nonneg hx 3]

theorem solution (x : ℝ) (hx : x > 0) (h'x : x ≠ 1) :
    4 * x ^ 6 - 3 * x ^ 5 + x ^ 4 + 5 * x ^ 3 + 2 * x ^ 2 - x + 1 > 0 := by
  have h := nonnegative_lower_bound x (le_of_lt hx)
  linarith

-- Prove2me | solution 1 for lean_workbook_plus_80043
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:58:00.897544+00:00
-- url     : https://prove2.me/submissions/29f5d242-adee-4679-a627-0d8e7c30a7ce

import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

theorem solution (a b : ℝ) :
    Real.sqrt (a ^ 2 + b ^ 2 + a * b) ≥ Real.sqrt 3 / 2 * (a + b) := by
  apply Real.le_sqrt_of_sq_le
  rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num
  nlinarith only [sq_nonneg (a - b)]

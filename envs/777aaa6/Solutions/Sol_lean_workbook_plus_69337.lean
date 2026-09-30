-- Prove2me | solution 1 for lean_workbook_plus_69337
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:37:50.225073+00:00
-- url     : https://prove2.me/submissions/30df9230-5273-407c-a7d9-c761b1e422fe

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (x y : ℝ) : Real.sqrt (x ^ 2 + x * y + y ^ 2) ≥
    Real.sqrt 3 / 2 * (x + y) := by
  apply Real.le_sqrt_of_sq_le
  rw [mul_pow, div_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  nlinarith [sq_nonneg (x - y)]

#print axioms solution

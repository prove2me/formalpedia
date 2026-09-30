-- Prove2me | solution 1 for lean_workbook_plus_67827
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:31:30.320391+00:00
-- url     : https://prove2.me/submissions/590fffd9-4048-4d7d-b99d-ffd7c65220bb

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a : ℝ) (h : a > 0) :
    a - 1 / 4 ≤ (a ^ 2 + 2) ^ 2 / (2 * Real.sqrt 3) ^ 2 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hd : (2 * Real.sqrt 3) ^ 2 = (12 : ℝ) := by nlinarith
  rw [hd]
  apply (le_div_iff₀ (show (0 : ℝ) < 12 by norm_num)).mpr
  nlinarith [mul_nonneg (sq_nonneg (a - 1))
    (show 0 ≤ (a + 1) ^ 2 + 6 by positivity)]

#print axioms solution

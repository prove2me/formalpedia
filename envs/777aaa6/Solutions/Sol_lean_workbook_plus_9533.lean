-- Prove2me | solution 1 for lean_workbook_plus_9533
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:44:19.889279+00:00
-- url     : https://prove2.me/submissions/09044291-1ff7-4a74-9764-bdf065e2c766

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (h : a * (a - b) + b * (b - c) + c * (c - a) = 0) : a = b ∧ b = c ∧ c = a := by
  have hsum : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 = 0 := by nlinarith [h]
  have h1 : (a - b) ^ 2 = 0 := by nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  have h2 : (b - c) ^ 2 = 0 := by nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  have h3 : (c - a) ^ 2 = 0 := by nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  refine ⟨?_, ?_, ?_⟩
  · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1; linarith
  · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2; linarith
  · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h3; linarith

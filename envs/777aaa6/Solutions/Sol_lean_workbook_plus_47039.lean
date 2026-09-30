-- Prove2me | solution 1 for lean_workbook_plus_47039
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:14:09.170093+00:00
-- url     : https://prove2.me/submissions/2303e523-115c-4817-8870-05f4f987ac79

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) : (a * b + a * c + b * c) / (a ^ 2 + b ^ 2 + c ^ 2) ≤ 1 := by
  rcases eq_or_lt_of_le (by positivity : (0:ℝ) ≤ a ^ 2 + b ^ 2 + c ^ 2) with h | h
  · rw [← h, div_zero]
    norm_num
  · rw [div_le_one h]
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]

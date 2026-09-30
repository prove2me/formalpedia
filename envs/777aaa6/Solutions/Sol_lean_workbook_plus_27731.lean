-- Prove2me | solution 1 for lean_workbook_plus_27731
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:36:02.891707+00:00
-- url     : https://prove2.me/submissions/4e8ffdd6-9a4b-450b-9d35-c6814fa408b9

import Mathlib.Analysis.Complex.Basic

theorem solution (f : ℝ → ℝ) (x : ℝ) : (4 * x ^ 2 - f x) * f x ≤ (4 * x ^ 2 - f x + f x) ^ 2 / 4 := by
  rw [le_div_iff₀ (by norm_num : (0:ℝ) < 4)]
  nlinarith [sq_nonneg (4 * x ^ 2 - 2 * f x)]

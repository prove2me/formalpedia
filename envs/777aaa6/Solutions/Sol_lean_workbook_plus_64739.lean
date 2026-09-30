-- Prove2me | solution 1 for lean_workbook_plus_64739
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:06:17.837897+00:00
-- url     : https://prove2.me/submissions/8131914a-f27c-4813-97f2-78119bc71e86

import Mathlib.Analysis.Complex.Basic

theorem solution (n : ℕ) (x : ℝ) (hx: x ≤ 1) : (1 - x)^n ≥ 1 - n*x := by
  have h := one_add_mul_le_pow (show (-2:ℝ) ≤ -x by linarith) n
  rw [ge_iff_le]
  convert h using 1 <;> ring

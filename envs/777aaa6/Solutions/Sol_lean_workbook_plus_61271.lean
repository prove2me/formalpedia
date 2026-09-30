-- Prove2me | solution 1 for lean_workbook_plus_61271
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:41:47.161604+00:00
-- url     : https://prove2.me/submissions/7efc0f2a-0b81-452c-b9e1-b2fc9ba86c75

import Mathlib.Analysis.Complex.Basic

theorem solution (x : ℝ) : 4*x^2+8*x+4 = 0 ↔ x = -1 := by
  constructor
  · intro h
    have h2 : (x + 1) ^ 2 = 0 := by nlinarith
    have h3 : x + 1 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
    linarith
  · rintro rfl
    norm_num

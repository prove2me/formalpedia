-- Prove2me | solution 1 for lean_workbook_plus_48247
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:50:12.650734+00:00
-- url     : https://prove2.me/submissions/afb87cb6-a2ca-44f7-af32-4389ec5a1521

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (n : ℕ) (hn : 0 < n) (x_n : ℝ) (hx_n : x_n = (3 + Real.sqrt 5)^n + (3 - Real.sqrt 5)^n) : 2^n ∣ x_n := by
  norm_num

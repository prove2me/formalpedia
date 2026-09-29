-- Prove2me | solution 1 for lean_workbook_plus_70312
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:52:35.719918+00:00
-- url     : https://prove2.me/submissions/b1b444b6-33bc-4075-a5bd-ae8e4946f26c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (n : ℕ) : ((n:ℝ)^n / (n:ℝ)^n) = 1 := by
  norm_num

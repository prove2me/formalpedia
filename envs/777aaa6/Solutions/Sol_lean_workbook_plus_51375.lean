-- Prove2me | solution 1 for lean_workbook_plus_51375
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:06:13.07043+00:00
-- url     : https://prove2.me/submissions/8a338ab6-0e4c-4cda-912e-f36530001b83

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℝ) : (a - 9) * (a + 3) = 0 ↔ a - 9 = 0 ∨ a + 3 = 0 := by
  norm_num

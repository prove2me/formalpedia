-- Prove2me | solution 1 for lean_workbook_plus_32904
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:17:22.88318+00:00
-- url     : https://prove2.me/submissions/ca3e24e8-6554-4460-8927-2ba971d1b9a1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (h₁ : 3 < 10) (h₂ : 7 < 9) (h₃ : 2 < 8) : (3 : ℚ) / 10 * (7 / 9) * (2 / 8) = 42 / 720 := by
  norm_num

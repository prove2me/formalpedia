-- Prove2me | solution 1 for lean_workbook_plus_25067
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:27:21.612166+00:00
-- url     : https://prove2.me/submissions/ecbfa514-4c11-40e4-8c64-5675bab30553

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (b c x : ℝ)
  (h₀ : b * c * x^2 = b * c * x^2) :
  b * c * x^2 = b * c * x^2 := by
  norm_num

-- Prove2me | solution 1 for lean_workbook_plus_38081
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:52:47.347998+00:00
-- url     : https://prove2.me/submissions/4973573e-fcbb-45ef-8c22-c8e6fd72182b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ)
  (h₀ : 96 * x = 72 * (14 - x)) :
  x = 6 := by
  (intros; linarith)

-- Prove2me | solution 1 for lean_workbook_plus_33359
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:06:35.4699+00:00
-- url     : https://prove2.me/submissions/2d6b4f6d-752a-40d3-993c-960ebf2e3051

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ)
  (h₀ : 0.6 * x = 36) :
  x = 60 := by
  (intros; linarith)

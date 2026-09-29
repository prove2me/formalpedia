-- Prove2me | solution 1 for lean_workbook_plus_73766
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:51:11.510686+00:00
-- url     : https://prove2.me/submissions/a862dcc7-0107-454c-8ecf-e58e7d0ca807

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h₁ : x^2 + x*y = 28) (h₂ : y^2 + x*y = -12) : (x + y)*(x - y) = 40 := by
  (intros; linarith)

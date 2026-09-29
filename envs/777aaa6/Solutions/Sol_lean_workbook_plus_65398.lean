-- Prove2me | solution 1 for lean_workbook_plus_65398
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:06:09.998928+00:00
-- url     : https://prove2.me/submissions/21c4c523-3a49-4dfb-b0eb-74bcf117adc6

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) : x^2 - 4*x + 8 = (x-4)^2 + 4*(x-4) + 8 := by
  (intros; linarith)

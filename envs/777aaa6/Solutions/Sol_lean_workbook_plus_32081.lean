-- Prove2me | solution 1 for lean_workbook_plus_32081
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:55:20.589856+00:00
-- url     : https://prove2.me/submissions/a536adc0-d32d-4bb0-99f3-64cfae14612a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (hx : x^5 + 1/x^5 + 10*4 + 5*52 = 1024) : x^5 + 1/x^5 = 724 := by
  (intros; linarith)

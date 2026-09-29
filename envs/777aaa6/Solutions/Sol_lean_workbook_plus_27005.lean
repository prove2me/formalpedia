-- Prove2me | solution 1 for lean_workbook_plus_27005
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:15:09.139611+00:00
-- url     : https://prove2.me/submissions/ac13cae7-b1a2-40e7-aa86-b341a5f5b11e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) : (x+1)*(x+2)*(x+9)*(x+14)-900*x = (x^2+28*x+252)*(x-1)^2 := by
  (intros; linarith)

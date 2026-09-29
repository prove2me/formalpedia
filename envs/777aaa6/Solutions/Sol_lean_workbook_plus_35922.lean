-- Prove2me | solution 1 for lean_workbook_plus_35922
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:38:29.968252+00:00
-- url     : https://prove2.me/submissions/8960dac6-046f-4225-b14e-322a61cb6fa6

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℤ) : x^18 - 1 = (x^9 - 1) * (x^9 + 1) := by
  (intros; linarith)

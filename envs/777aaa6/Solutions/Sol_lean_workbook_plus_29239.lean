-- Prove2me | solution 1 for lean_workbook_plus_29239
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:40:45.868254+00:00
-- url     : https://prove2.me/submissions/d5b576f7-afe0-41ed-8bf3-3f5dc86230a4

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (m : ℤ) :
  4 * m^4 + 1 = (2 * m^2 + 1)^2 - (2 * m)^2 := by
  (intros; linarith)

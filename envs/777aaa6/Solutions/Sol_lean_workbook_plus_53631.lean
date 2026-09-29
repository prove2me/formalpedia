-- Prove2me | solution 1 for lean_workbook_plus_53631
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:46:05.968941+00:00
-- url     : https://prove2.me/submissions/c4e8c893-2b48-485c-9f3a-60f666b0410d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) : (x^2 - y^2)^2 + (2 * x * y)^2 = (x^2 + y^2)^2 := by
  (intros; linarith)

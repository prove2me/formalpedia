-- Prove2me | solution 1 for lean_workbook_plus_68718
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:31:29.713198+00:00
-- url     : https://prove2.me/submissions/d32859f8-bbec-4e96-b1a8-425b411133cc

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) :
  x^3 + y^3 + z^3 - (x + y + z)^3 = -3 * (y + z) * (z + x) * (x + y) := by
  (intros; linarith)

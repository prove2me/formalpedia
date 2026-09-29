-- Prove2me | solution 1 for lean_workbook_plus_15185
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:14:00.842945+00:00
-- url     : https://prove2.me/submissions/36206832-5e21-41d8-91ff-1a6131efa971

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : x^3 + y^3 + z^3 - 3*x*y*z = (x + y + z)*(x^2 + y^2 + z^2 - x*y - x*z - y*z) := by
  (intros; linarith)

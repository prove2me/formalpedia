-- Prove2me | solution 1 for lean_workbook_plus_17959
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:56:01.329145+00:00
-- url     : https://prove2.me/submissions/159e4f3e-1d64-48dc-aad1-f78af62d6132

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : x^3 + y^3 + z^3 - 3*x*y*z = (x + y + z)*(x^2 + y^2 + z^2 - x*y - y*z - z*x) := by
  (intros; linarith)

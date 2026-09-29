-- Prove2me | solution 1 for lean_workbook_plus_8926
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:57:38.40872+00:00
-- url     : https://prove2.me/submissions/87255605-e252-47b7-9d49-ec8112676438

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : x^3 + y^3 + z^3 - 3*x*y*z = (x + y + z)*(x^2 + y^2 + z^2 - x*y - y*z - x*z) := by
  (intros; linarith)

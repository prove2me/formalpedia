-- Prove2me | solution 2 for lean_workbook_plus_10941
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:39:25.02553+00:00
-- url     : https://prove2.me/submissions/f17e3d45-21d0-4a62-859c-38dd4236f329

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (h : x*y*z = -2) : (x + y + z)^3 = x^3 + y^3 + z^3 + 6*x*y*z + 3*(x^2*y + x^2*z + y^2*x + y^2*z + z^2*x + z^2*y) := by
  (intros; linarith)

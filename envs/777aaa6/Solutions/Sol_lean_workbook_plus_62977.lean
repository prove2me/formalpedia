-- Prove2me | solution 1 for lean_workbook_plus_62977
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:17:55.684761+00:00
-- url     : https://prove2.me/submissions/a747f4db-af0c-4b76-81f7-70efcd9e6b61

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : (x^4+y^4+z^4-3*x^2*y*z-3*x*y^2*z-3*x*y*z^2+x^3*y+x*y^3+x^3*z+x*z^3+y^3*z+y*z^3) = (x+y+z)^2*(x^2+y^2+z^2-x*y-x*z-y*z) := by
  (intros; linarith)

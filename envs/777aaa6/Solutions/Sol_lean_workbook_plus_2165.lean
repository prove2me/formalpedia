-- Prove2me | solution 1 for lean_workbook_plus_2165
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:24:32.921274+00:00
-- url     : https://prove2.me/submissions/703f92f1-8a1a-4988-8cbd-95e945e1ab9d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d w x y z : ℝ) : (a^2+b^2+c^2+d^2)*(w^2+x^2+y^2+z^2) = (a*w+b*x+c*y+d*z)^2+(a*x-b*w+c*z-d*y)^2+(a*y-b*z-c*w+d*x)^2+(a*z+b*y-c*x-d*w)^2 := by
  (intros; linarith)

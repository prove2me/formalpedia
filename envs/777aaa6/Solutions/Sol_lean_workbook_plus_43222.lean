-- Prove2me | solution 1 for lean_workbook_plus_43222
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:10:01.716461+00:00
-- url     : https://prove2.me/submissions/3459ed2d-4052-4d76-bee1-b7172cad96d5

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y z : ℝ) :
  Real.sqrt ((x ^ 2 + y ^ 2 + z ^ 2) ^ 3) ≥ x ^ 3 + y ^ 3 + z ^ 3 - 3 * x * y * z := by
  apply Real.le_sqrt_of_sq_le
  have hs : 0≤4*(x^2+y^2+z^2)-(x+y+z)^2 := by nlinarith [sq_nonneg (x-y),sq_nonneg (y-z),sq_nonneg (z-x),sq_nonneg x,sq_nonneg y,sq_nonneg z]
  have hp := mul_nonneg (sq_nonneg (x^2+y^2+z^2-(x+y+z)^2)) hs
  nlinarith only [hp]

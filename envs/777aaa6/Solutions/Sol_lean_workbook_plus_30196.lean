-- Prove2me | solution 1 for lean_workbook_plus_30196
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:06:59.133477+00:00
-- url     : https://prove2.me/submissions/41d987d2-75d1-40b6-ae94-6d4746bd98d2

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c x y z : ℝ) (h : x^3 + y^3 + z^3 = 3 * x * y * z) :
  (a^2 + b^2 + c^2) * (x^2 + y^2 + z^2) + 2 * (a * b + b * c + c * a) * (x * y + y * z + z * x) ≥ 0 := by
  have ha : 0≤a^2+b^2+c^2-a*b-b*c-c*a := by nlinarith [sq_nonneg (a-b),sq_nonneg (b-c),sq_nonneg (c-a)]
  have hx : 0≤x^2+y^2+z^2-x*y-y*z-z*x := by nlinarith [sq_nonneg (x-y),sq_nonneg (y-z),sq_nonneg (z-x)]
  have hp := mul_nonneg ha hx
  nlinarith only [hp,sq_nonneg ((a+b+c)*(x+y+z))]

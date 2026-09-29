-- Prove2me | solution 1 for lean_workbook_plus_64070
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:17:28.998054+00:00
-- url     : https://prove2.me/submissions/82f63560-acdd-4eee-823b-c98b35839549

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (y + z) / x + (z + x) / y + (x + y) / z >= 3 * (1 + (x ^ 2 + y ^ 2 + z ^ 2) / (x * y + y * z + z * x)) := by
  have hp : 0<x*y+y*z+z*x := by positivity
  have hi : (y+z)/x+(z+x)/y+(x+y)/z-3*(1+(x^2+y^2+z^2)/(x*y+y*z+z*x))=(x+y+z)*((x*y-y*z)^2+(y*z-z*x)^2+(z*x-x*y)^2)/(2*x*y*z*(x*y+y*z+z*x)) := by field_simp; ring
  have hn : 0≤(x+y+z)*((x*y-y*z)^2+(y*z-z*x)^2+(z*x-x*y)^2)/(2*x*y*z*(x*y+y*z+z*x)) := by positivity
  linarith

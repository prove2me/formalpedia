-- Prove2me | solution 1 for lean_workbook_plus_23175
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:50:57.190596+00:00
-- url     : https://prove2.me/submissions/901ee565-16dc-4651-bac5-94d450a44871

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution {x y z : ℂ} (h : x + y + z = 0) : x ^ 3 + y ^ 3 + z ^ 3 = 3 * x * y * z := by
  linear_combination (x^2+y^2+z^2-x*y-y*z-z*x)*h

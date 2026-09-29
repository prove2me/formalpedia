-- Prove2me | solution 1 for lean_workbook_plus_12331
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:54:32.560075+00:00
-- url     : https://prove2.me/submissions/71758e64-bf88-497b-9299-2b6fdd5cd7cc

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 1 / (2 * x * y * z)) :  Real.sqrt (1 + x^4 + y^4 + z^4) ≥ x * y + y * z + z * x := by
  have hd : 2*x*y*z ≠ 0 := by positivity
  have he := (eq_div_iff hd).mp h
  apply Real.le_sqrt_of_sq_le
  nlinarith [sq_nonneg (x^2-y^2),sq_nonneg (y^2-z^2),sq_nonneg (z^2-x^2)]

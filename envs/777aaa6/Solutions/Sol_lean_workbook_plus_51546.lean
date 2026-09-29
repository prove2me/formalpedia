-- Prove2me | solution 1 for lean_workbook_plus_51546
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:58:56.083555+00:00
-- url     : https://prove2.me/submissions/1cd6944b-fdfc-45e4-a6e2-cf05430a0023

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) : (x^3 + y^3 + z^3) * (x + y + z) ≥ (x^2 + y^2 + z^2)^2 := by
  nlinarith [mul_nonneg (mul_nonneg hx hy) (sq_nonneg (x-y)), mul_nonneg (mul_nonneg hy hz) (sq_nonneg (y-z)), mul_nonneg (mul_nonneg hz hx) (sq_nonneg (z-x))]

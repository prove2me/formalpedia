-- Prove2me | solution 1 for lean_workbook_plus_39031
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:09:25.43426+00:00
-- url     : https://prove2.me/submissions/740fa025-7f9d-4ff2-9f69-b19a848a7787

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x y z : ℝ) (hx : x>0) (hy : y>0) (hz : z>0) (habc : x*y*z = 1) : 4*x + y^3*z + y*z^3 >= 6 * (x^4*y^4*z^4)^(1/6) := by
  have hv : 0 < y*z := mul_pos hy hz
  have hbase : 3 ≤ 2*x+(y*z)^2 := by
    apply (mul_le_mul_iff_right₀ hv).mp
    have hp := mul_nonneg (sq_nonneg (y*z-1)) (show 0 ≤ y*z+2 by positivity)
    nlinarith
  have hp := mul_nonneg hv.le (sq_nonneg (y-z))
  norm_num
  nlinarith

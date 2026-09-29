-- Prove2me | solution 1 for lean_workbook_plus_62049
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:19:23.084558+00:00
-- url     : https://prove2.me/submissions/3d78206a-1cd3-483e-8297-367c672d00f1

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x y z : ℝ) (hx : x ≥ 2) (hy : y ≥ 2) (hz : z ≥ 2) : 3 * (x + y + z) ≤ x*y*z + x + 8 := by
  have hx0 : 0 ≤ x-2 := by linarith
  have hy0 : 0 ≤ y-2 := by linarith
  have hz0 : 0 ≤ z-2 := by linarith
  have hp := mul_nonneg hx0 hy0
  have hq := mul_nonneg hx0 hz0
  have hr := mul_nonneg hy0 hz0
  have hs := mul_nonneg hp hz0
  nlinarith

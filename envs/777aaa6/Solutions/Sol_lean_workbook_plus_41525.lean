-- Prove2me | solution 1 for lean_workbook_plus_41525
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T23:09:33.979182+00:00
-- url     : https://prove2.me/submissions/37b01ad3-9e0d-41d8-b980-22ed31933760

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (h : x^3 + y^4 ≤ x^2 + y^3) : x^3 + y^3 ≤ 2 := by
  nlinarith [mul_nonneg (sq_nonneg (x-1)) (by positivity : 0 ≤ 2*x+1), mul_nonneg (sq_nonneg (y-1)) (by positivity : 0 ≤ 3*y^2+2*y+1)]

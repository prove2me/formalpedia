-- Prove2me | solution 1 for lean_workbook_plus_11838
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:32:52.546385+00:00
-- url     : https://prove2.me/submissions/6353d5ed-75b9-4c6d-a78d-9adec70b0de6

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y z : ℝ) (hx : x > -1) (hy : y > -1) (hz : z > -1) (h : x^3 + y^3 + z^3 ≥ x^2 + y^2 + z^2) : x^5 + y^5 + z^5 ≥ x^2 + y^2 + z^2 := by
  have hx' := mul_nonneg (mul_nonneg (sq_nonneg x) (sq_nonneg (x-1))) (show 0 ≤ x+2 by linarith)
  have hy' := mul_nonneg (mul_nonneg (sq_nonneg y) (sq_nonneg (y-1))) (show 0 ≤ y+2 by linarith)
  have hz' := mul_nonneg (mul_nonneg (sq_nonneg z) (sq_nonneg (z-1))) (show 0 ≤ z+2 by linarith)
  nlinarith

-- Prove2me | solution 1 for lean_workbook_plus_29043
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:20:43.686358+00:00
-- url     : https://prove2.me/submissions/3593561d-52b3-46ad-9ddc-6c1396257625

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y z : ℝ) (hx : 1 < x) (hy : 1 < y) (hz : 1 < z) : x * (2 * y * z - y - z) + 1 - y * z ≥ 0 := by
  have h1 : 0 ≤ (y-1)*(z-1) := mul_nonneg (by linarith) (by linarith)
  have h2 : 0 ≤ 2*y*z-y-z := by nlinarith [mul_nonneg (by linarith : 0 ≤ y-1) (by linarith : 0 ≤ z)]
  nlinarith [mul_nonneg (by linarith : 0 ≤ x-1) h2]

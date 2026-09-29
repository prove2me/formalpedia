-- Prove2me | solution 1 for lean_workbook_plus_14749
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:04:47.120187+00:00
-- url     : https://prove2.me/submissions/ffad106f-f696-4f63-94be-edea90ae44e3

import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y z : ℝ) (hx : x ≥ -1) (hy : y ≥ -1) (hz : z ≥ -1) (h : x^3 + y^3 + z^3 ≥ x^2 + y^2 + z^2) : x^5 + y^5 + z^5 ≥ x^2 + y^2 + z^2 := by
  have hxq := mul_nonneg (mul_nonneg (sq_nonneg x) (sq_nonneg (x-1))) (show 0 ≤ x+2 by linarith)
  have hyq := mul_nonneg (mul_nonneg (sq_nonneg y) (sq_nonneg (y-1))) (show 0 ≤ y+2 by linarith)
  have hzq := mul_nonneg (mul_nonneg (sq_nonneg z) (sq_nonneg (z-1))) (show 0 ≤ z+2 by linarith)
  nlinarith

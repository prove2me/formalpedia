-- Prove2me | solution 1 for lean_workbook_plus_32272
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:00:12.754619+00:00
-- url     : https://prove2.me/submissions/9740b4f4-095c-4aa7-869c-728803b52380

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (5 * a ^ 2 + (b + c) ^ 2) ≤ (5 * a + 2 * (b + c)) / (9 * (a + b + c) ^ 2)) := by
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith [mul_nonneg (sq_nonneg (2*a-b-c)) (show 0 ≤ 2*a+b+c by positivity)]

-- Prove2me | solution 1 for lean_workbook_plus_9622
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:22:20.772916+00:00
-- url     : https://prove2.me/submissions/64f2a4ae-a70a-457e-becb-cf296e3fc14e

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : (a + b + c) * (a * b + b * c + c * a) ≥ 9 * a * b * c := by
  nlinarith [mul_nonneg ha (sq_nonneg (b-c)),mul_nonneg hb (sq_nonneg (c-a)),mul_nonneg hc (sq_nonneg (a-b))]

-- Prove2me | solution 1 for lean_workbook_plus_18225
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:22:11.149808+00:00
-- url     : https://prove2.me/submissions/b58a1e4b-d77d-48a0-bd2d-265b00f3a173

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℝ) (hx : 0 ≤ x ∧ x < 2) : 1 / (2 - x) ≥ (1 + x ^ 2) / 2 := by
  apply (div_le_div_iff₀ (by norm_num : (0:ℝ)<2) (by linarith : 0<2-x)).2
  nlinarith [mul_nonneg hx.1 (sq_nonneg (x-1))]

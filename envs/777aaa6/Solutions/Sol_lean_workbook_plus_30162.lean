-- Prove2me | solution 1 for lean_workbook_plus_30162
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:15:23.852002+00:00
-- url     : https://prove2.me/submissions/cd4a0aab-0ca3-43bf-ae43-16f2771461ed

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (a^4 + b^4) / (a^3 + b^3) ≥ (a^2 + b^2) / (a + b) := by
  apply (div_le_div_iff₀ (add_pos ha hb) (by positivity : 0 < a^3+b^3)).2
  nlinarith [mul_nonneg (mul_nonneg (le_of_lt (mul_pos ha hb)) (le_of_lt (add_pos ha hb))) (sq_nonneg (a-b))]

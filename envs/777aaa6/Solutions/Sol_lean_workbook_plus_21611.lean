-- Prove2me | solution 1 for lean_workbook_plus_21611
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:54:07.467952+00:00
-- url     : https://prove2.me/submissions/dadf9950-5500-4190-97ba-402c3c45f067

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (x : ℝ) (hx: x ≥ 0) : (1 / (1 + x ^ 2)) ≥ 1 - x / 2 := by
  have hd : 0 < 1+x^2 := by positivity
  apply (le_div_iff₀ hd).2
  nlinarith [mul_nonneg hx (sq_nonneg (x-1))]

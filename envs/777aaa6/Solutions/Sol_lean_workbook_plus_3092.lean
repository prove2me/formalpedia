-- Prove2me | solution 1 for lean_workbook_plus_3092
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:18:25.079507+00:00
-- url     : https://prove2.me/submissions/92ef0b23-7adf-4825-92fc-81c6d693eaad

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a ≥ 3) (hbc : a / 3 + b / 2 ≥ 2) (habc : a / 3 + b / 2 + c ≥ 3) : a ^ 3 + b ^ 3 + c ^ 3 ≥ 36 := by
  have h1 := mul_nonneg (sq_nonneg (a-3)) (show 0 ≤ a+6 by positivity)
  have h2 := mul_nonneg (sq_nonneg (b-2)) (show 0 ≤ b+4 by positivity)
  have h3 := mul_nonneg (sq_nonneg (c-1)) (show 0 ≤ c+2 by positivity)
  nlinarith

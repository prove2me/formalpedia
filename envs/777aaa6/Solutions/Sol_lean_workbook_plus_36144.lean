-- Prove2me | solution 1 for lean_workbook_plus_36144
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:23:24.006003+00:00
-- url     : https://prove2.me/submissions/9eaadff0-e84c-4974-b7a8-220a46e59e02

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2)^2 ≥ (a + b + c) * (a + b - c) * (a + c - b) * (b + c - a) := by
  nlinarith [sq_nonneg (a^2+b^2-c^2),sq_nonneg (a^2-b^2)]

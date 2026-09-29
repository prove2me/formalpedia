-- Prove2me | solution 1 for lean_workbook_plus_37530
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:17:49.319015+00:00
-- url     : https://prove2.me/submissions/93c05af9-2187-404e-a569-32f286077346

import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : Real.sqrt ((a^2 + b^2 + a * b) * (a^2 + c^2 + a * c)) ≥ a^2 + (a * (b + c)) / 2 + b * c := by
  apply Real.le_sqrt_of_sq_le
  nlinarith [mul_nonneg (sq_nonneg a) (sq_nonneg (b-c))]

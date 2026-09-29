-- Prove2me | solution 1 for lean_workbook_plus_31186
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:23:15.825472+00:00
-- url     : https://prove2.me/submissions/f8fc701a-a2bb-42fc-a15d-08ce9f11406d

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution :  ∀ a b c : ℝ, 100 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 - 192 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) ≥ 0 := by
  intro a b c
  nlinarith only [sq_nonneg (a^2),sq_nonneg (b^2),sq_nonneg (c^2),mul_nonneg (sq_nonneg a) (sq_nonneg b),mul_nonneg (sq_nonneg b) (sq_nonneg c),mul_nonneg (sq_nonneg c) (sq_nonneg a)]

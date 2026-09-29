-- Prove2me | solution 1 for lean_workbook_plus_2438
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:24:50.858472+00:00
-- url     : https://prove2.me/submissions/719424eb-b8fa-4633-b808-c97fcec1d1a5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^3 + b^3 + c^3 + a * b^2 + b * c^2 + c * a^2 ≥ 2 * (a^2 * b + b^2 * c + c^2 * a) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])

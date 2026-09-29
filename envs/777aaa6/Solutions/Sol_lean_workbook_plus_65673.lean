-- Prove2me | solution 1 for lean_workbook_plus_65673
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:06:22.658586+00:00
-- url     : https://prove2.me/submissions/b47618d5-a62e-443d-8b8f-17a19b1c4317

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) : a^3 + b^3 ≥ a^2 * b + b^2 * a := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb])

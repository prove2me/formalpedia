-- Prove2me | solution 1 for lean_workbook_plus_25929
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:35:10.679551+00:00
-- url     : https://prove2.me/submissions/e76f0b08-c9d5-41bf-aa00-737943cf6f31

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : 9 * (a^3 + b^3 + c^3) ≥ (a + b + c)^3 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc])

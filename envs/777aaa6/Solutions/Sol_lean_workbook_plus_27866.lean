-- Prove2me | solution 1 for lean_workbook_plus_27866
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:06:24.266847+00:00
-- url     : https://prove2.me/submissions/a1821b56-0772-498d-8d38-280b1bad89f8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (hab : a^2 + b * c = 1) : (1 - a^2)^2 + (1 - b^2)^2 + (1 - c^2)^2 ≥ 2 / 3 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])

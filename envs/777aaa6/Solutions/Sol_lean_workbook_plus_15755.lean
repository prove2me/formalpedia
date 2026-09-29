-- Prove2me | solution 1 for lean_workbook_plus_15755
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:14:39.537314+00:00
-- url     : https://prove2.me/submissions/52936898-55fd-4839-8e00-ef1c7440c248

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (hab : a + b^2 + c^2 = 1) :  a * b * c * (a + 1) * (b + 1) * (c + 1) ≤ 27 / 64 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])

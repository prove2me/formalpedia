-- Prove2me | solution 1 for lean_workbook_plus_22988
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:47:08.968302+00:00
-- url     : https://prove2.me/submissions/f2d13422-5098-4281-8f8a-732e779fb2f5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (habc : a * b * c * d = 1) (h : a^2 + b^2 + c^2 + d^2 = 1) : a + b + c + d + 1 / (a * b * c * d) ≥ 18 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (d), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a + d), sq_nonneg (b + c), sq_nonneg (b + d), sq_nonneg (c + d), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])

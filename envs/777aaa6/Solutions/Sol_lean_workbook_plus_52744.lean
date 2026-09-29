-- Prove2me | solution 1 for lean_workbook_plus_52744
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:03:58.178467+00:00
-- url     : https://prove2.me/submissions/fb94e8b8-4160-4224-8267-3bd9fce9e298

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hab : a^2 + b^2 = c^2 + d^2) : (a + b) * (c + d) ≥ 2 * (a * b + c * d) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (d), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a + d), sq_nonneg (b + c), sq_nonneg (b + d), sq_nonneg (c + d), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])

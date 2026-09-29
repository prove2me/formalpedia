-- Prove2me | solution 1 for lean_workbook_plus_22586
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:37:38.286071+00:00
-- url     : https://prove2.me/submissions/4055ba76-f815-432f-a289-03830bbd61ad

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^2 * b + b^2 * c + c^2 * a + a^3 + b^3 + c^3 ≥ 2 * (a * b^2 + b * c^2 + c * a^2) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])

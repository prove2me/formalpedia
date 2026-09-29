-- Prove2me | solution 1 for lean_workbook_plus_56566
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:23:25.338956+00:00
-- url     : https://prove2.me/submissions/3cb274ad-aeba-4f49-9cd8-b0bf30cc57c5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 2 * (a^3 + b^3 + c^3) ≥ a^2 * (b + c) + b^2 * (c + a) + c^2 * (b + a) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])

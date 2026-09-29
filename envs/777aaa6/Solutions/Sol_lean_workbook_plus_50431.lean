-- Prove2me | solution 1 for lean_workbook_plus_50431
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:20:33.06641+00:00
-- url     : https://prove2.me/submissions/6a2d33ac-964f-47d7-a64a-a2e8e07af2fe

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) : a^3 + b^3 + c^3 + d^3 ≥ 1 / 2 * (a + b + c + d) * (a * c + b * d) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (d), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a + d), sq_nonneg (b + c), sq_nonneg (b + d), sq_nonneg (c + d), mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc])

-- Prove2me | solution 1 for lean_workbook_plus_81056
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:36:31.899064+00:00
-- url     : https://prove2.me/submissions/a2e5125b-76f2-4de8-a551-3d7228d1e03c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hab : a * b * c * d = 1) : a^2 + b^2 + c^2 + d^2 = 1 → 1 / (a^2 * b^2 * c * d) + 1 / (a^2 * b * c^2 * d) + 1 / (a^2 * b * c * d^2) + 1 / (a * b^2 * c^2 * d) + 1 / (a * b^2 * c * d^2) + 1 / (a * b * c^2 * d^2) ≥ 384 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (d), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a + d), sq_nonneg (b + c), sq_nonneg (b + d), sq_nonneg (c + d), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])

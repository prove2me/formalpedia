-- Prove2me | solution 1 for lean_workbook_plus_81149
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:37:04.760716+00:00
-- url     : https://prove2.me/submissions/187980b3-37eb-4327-9b09-0cddcc227545

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : 3 * a ^ 2 * d ^ 2 + 3 * b ^ 2 * c ^ 2 + 2 * a ^ 2 * c ^ 2 + 2 * b ^ 2 * d ^ 2 + 5 * a * b * c * d ≥ 3 * a ^ 2 * c * d + 3 * d ^ 2 * a * b + 3 * c ^ 2 * a * b + 3 * b ^ 2 * c * d := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (d), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a + d), sq_nonneg (b + c), sq_nonneg (b + d), sq_nonneg (c + d), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])

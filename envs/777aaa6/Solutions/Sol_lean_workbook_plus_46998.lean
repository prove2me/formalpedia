-- Prove2me | solution 1 for lean_workbook_plus_46998
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:51:41.06673+00:00
-- url     : https://prove2.me/submissions/e103ce86-7afe-4b6c-836f-a5b095784069

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 5 * (a ^ 3 + b ^ 3 + c ^ 3) + 3 * (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) ≥ 6 * (a * b ^ 2 + b * c ^ 2 + c * a ^ 2) + 6 * a * b * c := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])

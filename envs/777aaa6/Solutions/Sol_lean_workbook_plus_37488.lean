-- Prove2me | solution 1 for lean_workbook_plus_37488
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:53:40.810253+00:00
-- url     : https://prove2.me/submissions/b31aab03-1d1a-4b60-b98f-6f0f307c910f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b + b * c + c * a = a * b * c) : (3 * a + 2 * b + c) * (3 * b + 2 * c + a) * (3 * c + 2 * a + b) ≥ 24 * a * b * c * (a + b + c) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])

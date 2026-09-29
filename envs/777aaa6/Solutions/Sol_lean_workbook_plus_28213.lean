-- Prove2me | solution 1 for lean_workbook_plus_28213
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:05:50.715088+00:00
-- url     : https://prove2.me/submissions/f351131c-67b6-4bbe-8b34-d2b3709eb1bf

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^3 + b^3 + c^3 ≥ 3 * a * b * c := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])

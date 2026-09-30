-- Prove2me | solution 2 for lean_workbook_plus_1961
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:25:29.045015+00:00
-- url     : https://prove2.me/submissions/a81a757a-95bb-4c8e-8967-62864aa335fd

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / (a + b) + b^2 / (b + c)) ≥ (3 * a + 2 * b - c) / 4 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])

-- Prove2me | solution 1 for lean_workbook_plus_24961
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:27:27.496762+00:00
-- url     : https://prove2.me/submissions/c584d02a-0d63-4f88-ae9e-65d196eb66fe

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * b / (a + 2 * b) + b * c / (b + 2 * c) + c * a / (c + 2 * a) : ℝ) ≤ (a + b + c) / 3 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])

-- Prove2me | solution 1 for lean_workbook_plus_28418
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:05:39.557221+00:00
-- url     : https://prove2.me/submissions/6e2a8ea3-a1a5-47f4-b411-352a28641a1e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b + c) ^ 3 ≥ (9 / 4) * ((a + b) ^ 2 * c + (b + c) ^ 2 * a + (c + a) ^ 2 * b) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])

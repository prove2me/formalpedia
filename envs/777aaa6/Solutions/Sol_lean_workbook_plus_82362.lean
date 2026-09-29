-- Prove2me | solution 1 for lean_workbook_plus_82362
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:35:37.253361+00:00
-- url     : https://prove2.me/submissions/902a61b0-8622-4afe-b35a-8ed7713764d8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b - c) / (a + b + 3 * c) + (b + c - a) / (3 * a + b + c) + (c + a - b) / (a + 3 * b + c) ≥ 3 / 5 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])

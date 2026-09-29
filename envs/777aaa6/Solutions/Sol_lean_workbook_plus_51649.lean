-- Prove2me | solution 1 for lean_workbook_plus_51649
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:06:05.688924+00:00
-- url     : https://prove2.me/submissions/ed914c4a-1260-4987-aad0-b1963efb31d5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (5 * a + 2 * b + c) + b / (a + 5 * b + 2 * c) + c / (2 * a + b + 5 * c) ≤ 3 / 8) := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])

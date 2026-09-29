-- Prove2me | solution 1 for lean_workbook_plus_30449
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:55:03.13757+00:00
-- url     : https://prove2.me/submissions/1c831f16-9983-4956-b61e-a21c6383a597

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (a + 2 * (b + c)) + b / (b + 2 * (c + a)) + c / (c + 2 * (a + b))) ≥ 3 / 5 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])

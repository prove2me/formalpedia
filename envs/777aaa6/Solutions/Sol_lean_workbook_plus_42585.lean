-- Prove2me | solution 1 for lean_workbook_plus_42585
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:17:01.062595+00:00
-- url     : https://prove2.me/submissions/d727f5b8-047c-4843-9c53-a8e75b323370

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a * b + b * c + c * a + (a + b + c) ^ 2 ≥ 9 * (a + b) * (b + c) * (c + a) / (2 * (a + b + c)) := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])

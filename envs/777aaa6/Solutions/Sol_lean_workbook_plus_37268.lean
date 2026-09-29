-- Prove2me | solution 1 for lean_workbook_plus_37268
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:54:01.076635+00:00
-- url     : https://prove2.me/submissions/8b31a6b0-a901-414e-82b3-fb8648c54c50

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (2 * a + b + c) + b / (a + 2 * b + c) + c / (a + b + 2 * c)) ≤ 3 / 4 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])

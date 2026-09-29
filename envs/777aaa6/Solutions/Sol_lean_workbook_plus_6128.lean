-- Prove2me | solution 1 for lean_workbook_plus_6128
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:06:45.120008+00:00
-- url     : https://prove2.me/submissions/34219f2e-883f-4c6b-a48e-abaf01cbf948

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hab : a + b ≥ 1 / 3 * (c + d)) (h : a^2 + b^2 = 1 / 3 * (c^2 + d^2)) : a^4 + a^2 * b^2 + b^4 ≤ 4 / 27 * (c^4 + c^2 * d^2 + d^4) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (d), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a + d), sq_nonneg (b + c), sq_nonneg (b + d), sq_nonneg (c + d), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])

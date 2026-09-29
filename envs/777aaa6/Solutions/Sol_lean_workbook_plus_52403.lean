-- Prove2me | solution 1 for lean_workbook_plus_52403
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:04:36.332532+00:00
-- url     : https://prove2.me/submissions/0b63fd41-615b-43a2-b401-b6382a69a2ed

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 2 * (1 / (a * b) + 1 / (b * c) + 1 / (c * a)) ≤ (2 / 3) * (1 / a + 1 / b + 1 / c)^2 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])

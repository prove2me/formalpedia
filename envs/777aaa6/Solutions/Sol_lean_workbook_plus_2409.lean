-- Prove2me | solution 1 for lean_workbook_plus_2409
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:26:05.446332+00:00
-- url     : https://prove2.me/submissions/9407b2d4-0332-4d2a-ba7c-8cfdd3828d99

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / (b + 2 * c) + b / (c + 2 * a) + c / (a + 2 * b) ≥ 1 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])

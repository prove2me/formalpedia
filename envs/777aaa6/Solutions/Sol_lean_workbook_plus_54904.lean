-- Prove2me | solution 1 for lean_workbook_plus_54904
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:02:04.762905+00:00
-- url     : https://prove2.me/submissions/3feafec4-7a48-49a5-914c-09e6933a02fd

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 1 / a ^ 2 + 1 / b ^ 2 + 1 / c ^ 2 ≥ (a + b + c) / (a * b * c) := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])

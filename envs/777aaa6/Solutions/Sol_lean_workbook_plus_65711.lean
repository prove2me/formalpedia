-- Prove2me | solution 1 for lean_workbook_plus_65711
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:05:48.612589+00:00
-- url     : https://prove2.me/submissions/8f1fdd73-92be-4c8a-b169-71e0db703706

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) : 4 * (a^2 / b / c + b^2 / c / a + c^2 / a / b) + 729 * a * b * c ≥ 39 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])

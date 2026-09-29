-- Prove2me | solution 1 for lean_workbook_plus_43073
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:16:16.304674+00:00
-- url     : https://prove2.me/submissions/f19fc859-0763-403f-88ae-9aab680e3f8f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (hab : 2 * a + b + c ≤ 3 / 2) : a^2 + b * c + 2 / a + 1 / b + 1 / c ≥ 1051 / 96 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])

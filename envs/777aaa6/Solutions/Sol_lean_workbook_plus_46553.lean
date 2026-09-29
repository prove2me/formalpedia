-- Prove2me | solution 1 for lean_workbook_plus_46553
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:14:58.232784+00:00
-- url     : https://prove2.me/submissions/7ad5a4ea-f6a3-4d9c-825e-e370ccf9f16e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)(habc : a * b * c = 1) (hab : a + b + c ≤ 3 / 2) : a + b + c + 1 / a + 1 / b + 1 / c ≥ 15 / 2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])

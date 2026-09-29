-- Prove2me | solution 1 for lean_workbook_plus_33834
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:15:37.775014+00:00
-- url     : https://prove2.me/submissions/20be8462-9344-4298-92c3-60dd4e28ff73

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1 / 3) : (a + b + c) * (1 + 1 / a / b / c) ≥ 28 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])

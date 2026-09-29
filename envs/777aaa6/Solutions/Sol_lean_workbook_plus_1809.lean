-- Prove2me | solution 1 for lean_workbook_plus_1809
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:32:43.245697+00:00
-- url     : https://prove2.me/submissions/0020a3b8-931a-48e3-9563-5d276c2907ed

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h : a + b + c ≥ 3 * a * b * c) : a ^ 2 + b ^ 2 + c ^ 2 ≥ 2 * a * b * c := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])

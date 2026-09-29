-- Prove2me | solution 1 for lean_workbook_plus_28459
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:05:36.739261+00:00
-- url     : https://prove2.me/submissions/47bb49ef-1390-4921-a097-8ae196054309

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : 3 * a ^ 2 + (b + c) ^ 2 > 4 * a * c := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])

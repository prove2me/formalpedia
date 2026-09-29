-- Prove2me | solution 1 for lean_workbook_plus_61182
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:32:20.337006+00:00
-- url     : https://prove2.me/submissions/6fd4ee81-50ee-4fd5-824d-fcf75538be81

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (hab : a + b + c = 3) (h : a > 0 ∧ b > 0 ∧ c > 0)(habc : a * b * c = 1) : a ^ 2 + b ^ 2 + c ^ 2 ≥ a + b + c := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])

-- Prove2me | solution 2 for lean_workbook_plus_76682
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:27:24.662931+00:00
-- url     : https://prove2.me/submissions/56c4ee36-c0c6-4a61-8b3f-f1dfc324935f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : (a + b) * (b + c) * (c + a) / 8 ≥ (2 * a + b) * (2 * b + c) * (2 * c + a) / 27 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])

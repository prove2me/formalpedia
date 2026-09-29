-- Prove2me | solution 1 for lean_workbook_plus_79910
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:00:07.64651+00:00
-- url     : https://prove2.me/submissions/edb46bec-d42d-4ead-a490-64dfa35a231c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h : a + b + a * b = 3) (h1 : a > 0 ∧ b > 0 ∧ c > 0): a + b >= 2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])

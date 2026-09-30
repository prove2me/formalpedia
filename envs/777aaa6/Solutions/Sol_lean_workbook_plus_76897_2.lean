-- Prove2me | solution 2 for lean_workbook_plus_76897
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:25:46.639773+00:00
-- url     : https://prove2.me/submissions/5e9623ea-5b03-4d56-b671-0f3f19523fa2

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : 2 * (a ^ 4 + b ^ 4 + c ^ 4) ≥ a ^ 3 * b + a ^ 3 * c + b ^ 3 * a + b ^ 3 * c + c ^ 3 * a + c ^ 3 * b := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])

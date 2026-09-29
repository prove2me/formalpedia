-- Prove2me | solution 1 for lean_workbook_plus_57613
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:46:01.190505+00:00
-- url     : https://prove2.me/submissions/df713ba2-23ad-474f-b2f7-4c88cca695c7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : a^4 + b^4 + c^4 + 3 * (b^2 * c^2 + c^2 * a^2 + a^2 * b^2) ≥ 2 * (b^3 * c + c^3 * b + c^3 * a + a^3 * c + a^3 * b + b^3 * a) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])

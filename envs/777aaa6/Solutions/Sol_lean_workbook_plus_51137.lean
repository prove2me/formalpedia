-- Prove2me | solution 1 for lean_workbook_plus_51137
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:19:09.507712+00:00
-- url     : https://prove2.me/submissions/ef2e1016-cfc9-4909-b426-3660b5de30ce

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (a^2+b^2+c^2)^2 ≥ (a * b + b * c + c * a)^2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])

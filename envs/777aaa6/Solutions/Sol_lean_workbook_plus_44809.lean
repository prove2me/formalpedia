-- Prove2me | solution 1 for lean_workbook_plus_44809
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:15:51.635031+00:00
-- url     : https://prove2.me/submissions/bc822483-fc23-4c04-b048-4ff969feb8a7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (hab : a ≥ b) (hbc : b ≥ c) : a^2 + a*c + c^2 ≥ 3*b*(a - b + c) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])

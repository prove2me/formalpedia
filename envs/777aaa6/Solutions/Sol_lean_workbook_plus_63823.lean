-- Prove2me | solution 1 for lean_workbook_plus_63823
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:49:55.79091+00:00
-- url     : https://prove2.me/submissions/3995393c-3129-4c84-b48f-67c359372f53

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h : c ≥ a ∧ a ≥ b) : a^2 + b^2 + c^2 - a * b - b * c - c * a ≥ 2 * (a - b) * (a - c) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])

-- Prove2me | solution 1 for lean_workbook_plus_66797
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:14:48.136864+00:00
-- url     : https://prove2.me/submissions/63ebb993-29f0-4117-acb5-1457f2ce7fe2

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (c : ℝ) (h : a ≥ b) (h2 : c ≥ 0) : a * c ≥ b * c := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])

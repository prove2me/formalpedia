-- Prove2me | solution 1 for lean_workbook_plus_25348
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:26:44.286086+00:00
-- url     : https://prove2.me/submissions/c96d3f82-0fa6-4109-8743-89c939779135

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h : a ≥ b ∧ b ≥ c) : (c - a) ^ 2 ≥ (a - b) ^ 2 + (b - c) ^ 2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])

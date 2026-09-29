-- Prove2me | solution 1 for lean_workbook_plus_54373
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:44:46.067948+00:00
-- url     : https://prove2.me/submissions/2f8135c6-fc52-4ad6-944b-c355a95399a0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h : a + b + c ≥ a * b * c) : a ^ 2 + b ^ 2 + c ^ 2 ≥ a * b * c := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])

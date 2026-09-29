-- Prove2me | solution 1 for lean_workbook_plus_18372
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:56:36.977965+00:00
-- url     : https://prove2.me/submissions/a2e28420-d4ee-415b-9276-ff25c04797a8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h : a + b + c = 1 / a + 1 / b + 1 / c) : a ^ 2 + b ^ 2 + c ^ 2 ≥ a * b + b * c + c * a := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])

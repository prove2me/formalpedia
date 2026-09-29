-- Prove2me | solution 1 for lean_workbook_plus_6525
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:06:24.528555+00:00
-- url     : https://prove2.me/submissions/0f53ddbb-86f5-4489-b57f-9af1ec78f604

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h : a + b + c = a * b * c) :
  (a^2 + 1) * (b^2 + 1) * (c^2 + 1) ≥ (a * b + b * c + c * a - 1)^2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])

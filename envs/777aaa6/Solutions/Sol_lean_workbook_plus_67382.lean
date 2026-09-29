-- Prove2me | solution 1 for lean_workbook_plus_67382
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:14:14.287556+00:00
-- url     : https://prove2.me/submissions/7b3fdca0-dd8c-43ad-9d51-d2d8ed9c8aac

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (A B : ℝ) (x y : ℝ) (h₁ : x^2 = (A + B) / 2) (h₂ : y^2 = (A - B) / 2) : x^2 + y^2 = A ∧ x^2 - y^2 = B := by
  (intros; constructor <;> nlinarith [sq_nonneg (A), sq_nonneg (B), sq_nonneg (x), sq_nonneg (y), sq_nonneg (A - B), sq_nonneg (A - x), sq_nonneg (A - y), sq_nonneg (B - x), sq_nonneg (B - y), sq_nonneg (x - y), sq_nonneg (A + B), sq_nonneg (A + x), sq_nonneg (A + y), sq_nonneg (B + x), sq_nonneg (B + y), sq_nonneg (x + y)])

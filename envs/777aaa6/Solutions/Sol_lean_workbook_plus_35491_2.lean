-- Prove2me | solution 2 for lean_workbook_plus_35491
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:42:36.488955+00:00
-- url     : https://prove2.me/submissions/850daee4-d3b7-4541-86e2-b330fd3f53ca

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ)
  (x y z : ℝ)
  (h₀ : x = a / b)
  (h₁ : y = b / c)
  (h₂ : z = c / a) :
  a^2 + b^2 + c^2 ≥ a * b + b * c + c * a := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (x), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - x), sq_nonneg (b - c), sq_nonneg (b - x), sq_nonneg (c - x), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a + x), sq_nonneg (b + c), sq_nonneg (b + x), sq_nonneg (c + x)])

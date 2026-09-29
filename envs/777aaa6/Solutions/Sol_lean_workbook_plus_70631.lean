-- Prove2me | solution 1 for lean_workbook_plus_70631
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:51:19.024984+00:00
-- url     : https://prove2.me/submissions/33c392ed-a8bd-4049-be7c-8cc22ca3c1e5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h₁ : 1 ≤ x ∧ x ≤ y - 1) (h₂ : 1 ≤ y) : x^2 - y * x ≤ 1 - y := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])

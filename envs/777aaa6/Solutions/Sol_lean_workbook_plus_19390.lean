-- Prove2me | solution 1 for lean_workbook_plus_19390
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:55:34.284499+00:00
-- url     : https://prove2.me/submissions/0ed4047d-98ff-462c-ae35-6cf3345ef515

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h₁ : y = x^2 + 1) : y ≥ 0 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])

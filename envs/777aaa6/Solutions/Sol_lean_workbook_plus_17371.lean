-- Prove2me | solution 1 for lean_workbook_plus_17371
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:06:04.648648+00:00
-- url     : https://prove2.me/submissions/147ba746-6f90-42e0-9a6c-54b08bda30fb

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (h₁ : a > b) : a^3 + a^2 * b ≥ b^3 + a * b^2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])

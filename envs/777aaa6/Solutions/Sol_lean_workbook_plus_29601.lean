-- Prove2me | solution 1 for lean_workbook_plus_29601
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:04:18.075752+00:00
-- url     : https://prove2.me/submissions/ecd48739-83fa-4d8e-8afc-d5a99136087f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h₁ : 0 < a ∧ 0 < b ∧ 0 < c) (h₂ : a ≤ b ∧ b ≤ c) :  (a + b) * (a + c) ^ 2 / 3 ≥ 2 * a * b * c := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])

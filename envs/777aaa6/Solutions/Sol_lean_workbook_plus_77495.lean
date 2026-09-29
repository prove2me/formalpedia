-- Prove2me | solution 1 for lean_workbook_plus_77495
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:02:11.652521+00:00
-- url     : https://prove2.me/submissions/86fe1894-9261-46f8-a767-024d972953ce

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (k a b c d : ℝ) (h₁ : 0 < k) (h₂ : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d) (h₃ : a ≤ k ∧ b ≤ k ∧ c ≤ k ∧ d ≤ k) : 2 * k ^ 2 - k * (a + b + c + d) + a * b + b * c + c * d + d * a ≥ 0 := by
  (intros; nlinarith [sq_nonneg (k), sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (k - a), sq_nonneg (k - b), sq_nonneg (k - c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (k + a), sq_nonneg (k + b), sq_nonneg (k + c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])

-- Prove2me | solution 1 for lean_workbook_plus_61517
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:31:42.595374+00:00
-- url     : https://prove2.me/submissions/c397d06c-7b02-429b-82cd-5c7596a771a8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h₁ : 2 * c ≥ a ∧ a ≥ b ∧ b ≥ c) (h₂ : c > 0) : a * b * c ≥ (2 * a - b) * (2 * b - c) * (2 * c - a) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])

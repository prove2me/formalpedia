-- Prove2me | solution 1 for lean_workbook_plus_20641
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:05:34.221817+00:00
-- url     : https://prove2.me/submissions/665026d7-d1ef-42f6-9043-3102db85ebf1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h₁ : a ≥ b) (h₂ : b ≥ c) : (a - b) * (b - c) ≥ 0 ∧ c - a ≤ 0 := by
  (intros; constructor <;> nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])

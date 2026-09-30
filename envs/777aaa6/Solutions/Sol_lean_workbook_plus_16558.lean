-- Prove2me | solution 1 for lean_workbook_plus_16558
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:17:42.478043+00:00
-- url     : https://prove2.me/submissions/3e4fbd21-9a4e-48f2-a0d6-e4f747bbc789

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c d : ℝ)
  (h₀ : ∀ x, a * x + b = c * x + d) :
  a = c ∧ b = d := by
  have h0 := h₀ 0
  have h1 := h₀ 1
  simp only [mul_zero, zero_add, mul_one] at h0 h1
  constructor <;> linarith

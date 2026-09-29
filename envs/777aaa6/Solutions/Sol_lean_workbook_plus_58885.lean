-- Prove2me | solution 1 for lean_workbook_plus_58885
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:44:18.114702+00:00
-- url     : https://prove2.me/submissions/1b34cc4e-8160-4523-bcf2-1f42597562f6

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (x₁ x₂ y₁ y₂ : ℝ) (h₁ : y₁ = f x₁) (h₂ : y₂ = f x₂) : (y₂ - y₁) / (x₂ - x₁) = (f x₂ - f x₁) / (x₂ - x₁) := by
  (intros; simp_all)

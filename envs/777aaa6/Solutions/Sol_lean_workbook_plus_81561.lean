-- Prove2me | solution 1 for lean_workbook_plus_81561
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:38:05.030442+00:00
-- url     : https://prove2.me/submissions/05d3ac68-2998-44f8-811a-4d3dc912b31e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f g : ℝ → ℝ) (a b : ℝ) (h₁ : a + 3 * b = 12) (h₂ : ∀ x, f x = 3 * x + a) (h₃ : ∀ x, g x = x / 3 + b) : ∃ a b, a + 3 * b = 12 ∧ (∀ x, f x = 3 * x + a) ∧ (∀ x, g x = x / 3 + b) := by
  (intros; simp_all)

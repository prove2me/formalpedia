-- Prove2me | solution 1 for lean_workbook_plus_80374
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:00:46.578929+00:00
-- url     : https://prove2.me/submissions/6d4c3d71-1d88-46c1-a041-e736dbb5541f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ)
  (f g : ℝ → ℝ)
  (h₀ : ∀ x, f x = x^2 - 1)
  (h₁ : ∀ x, g x = 1 / f x)
  (h₂ : g x = 0.5 * (1 / (x - 1) - 1 / (x + 1))) :
  g x = 0.5 * (1 / (x - 1) - 1 / (x + 1)) := by
  (intros; simp_all)

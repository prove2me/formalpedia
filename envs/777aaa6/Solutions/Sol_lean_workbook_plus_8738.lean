-- Prove2me | solution 1 for lean_workbook_plus_8738
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-04T22:53:04.764291+00:00
-- url     : https://prove2.me/submissions/4c5754fa-443c-4925-b944-d98f2c0aeefb

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem solution (y₁ y₂ : ℝ) (h₁ : y₁ ^ 3 + y₁ = y₂ ^ 3 + y₂) : y₁ = y₂ := by
  have hp : (y₁ - y₂) * (y₁ ^ 2 + y₁ * y₂ + y₂ ^ 2 + 1) = 0 := by nlinarith [h₁]
  have hpos : 0 < y₁ ^ 2 + y₁ * y₂ + y₂ ^ 2 + 1 := by
    nlinarith [sq_nonneg (y₁ + y₂), sq_nonneg y₁, sq_nonneg y₂]
  have := (mul_eq_zero.mp hp).resolve_right (ne_of_gt hpos)
  linarith

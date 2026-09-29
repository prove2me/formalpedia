-- Prove2me | solution 1 for lean_workbook_plus_10621
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:41:03.522746+00:00
-- url     : https://prove2.me/submissions/c0d506d0-3cb4-4116-851f-ca806ffdcda4

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ)
  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = a * x^2 + b * x + c)
  (h₁ : a ≠ 0) :
  -(b^2 - 4 * a * c) / (4 * a) = c - b^2 / (4 * a) := by
  (intros; field_simp; ring)

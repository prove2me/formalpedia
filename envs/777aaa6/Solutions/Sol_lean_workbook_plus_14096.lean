-- Prove2me | solution 1 for lean_workbook_plus_14096
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:31:23.498669+00:00
-- url     : https://prove2.me/submissions/f0f5ec0c-2e21-48ac-a405-be3f1d39007d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z t a b c d : ℝ) (h₁ : x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧ t ≠ 0) (h₂ : a = y / x ∧ b = z / y ∧ c = t / z ∧ d = x / t) : a * b * c * d = 1 := by
  (intros; simp_all)

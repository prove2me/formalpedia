-- Prove2me | solution 1 for lean_workbook_plus_72895
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:36:04.71262+00:00
-- url     : https://prove2.me/submissions/266d63d7-9ecd-459c-94b1-76f759a3bae8

import Mathlib

set_option autoImplicit false

theorem solution (x y : ℝ) (h₀ : x + y = 4 * (x * y))
    (h₁ : x ≠ 0 ∧ y ≠ 0) : 1 / x + 1 / y = (x + y) / (x * y) := by
  field_simp [h₁.1, h₁.2] <;> ring

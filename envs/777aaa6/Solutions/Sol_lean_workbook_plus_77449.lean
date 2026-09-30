-- Prove2me | solution 1 for lean_workbook_plus_77449
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:03:00.434122+00:00
-- url     : https://prove2.me/submissions/2eb78e00-add7-4258-9223-8f0d27f311a9

import Mathlib

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (a : ℝ)
    (h₁ : ∀ x, f x = 1 / 3 + a * (1 / (2 * x + 1) - 1 / 3)) :
    ∀ x, f x = a * 1 / (2 * x + 1) + (1 - a) * 1 / 3 := by
  intro x
  rw [h₁]
  ring

#print axioms solution

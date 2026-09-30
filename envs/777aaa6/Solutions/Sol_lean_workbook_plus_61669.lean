-- Prove2me | solution 1 for lean_workbook_plus_61669
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:55:42.682011+00:00
-- url     : https://prove2.me/submissions/f3b6342c-6e88-4443-b5b1-2ecdcbe5dee5

import Mathlib
set_option autoImplicit false

theorem solution : ∀ a b c : ℝ, a ∈ Set.Icc 0 1 ∧ b ∈ Set.Icc 0 1 ∧ c ∈ Set.Icc 0 1 ∧ a + b + c = 3 / 2 → 3 / 4 - (a * b + b * c + c * a) = (a - b) ^ 2 / 6 + (b - c) ^ 2 / 6 + (c - a) ^ 2 / 6 ∧ a * b + b * c + c * a - 1 / 2 = (1 - a) * (1 - b) * (1 - c) + a * b * c   := by
  intro a b c h
  have hc : c = 3 / 2 - a - b := by linarith [h.2.2.2]
  rw [hc]
  constructor <;> ring

#print axioms solution

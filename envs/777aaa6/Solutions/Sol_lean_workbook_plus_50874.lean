-- Prove2me | solution 1 for lean_workbook_plus_50874
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:16:52.716712+00:00
-- url     : https://prove2.me/submissions/add4e5fa-f966-4eeb-8fff-32e530e5063b

import Mathlib
set_option autoImplicit false

theorem solution : ∀ a : ℝ, (∃ x, x^2 - a*x + 2 = 0) → a^2 ≥ 8   := by
  intro a ha
  obtain ⟨x, hx⟩ := ha
  nlinarith [sq_nonneg (x - a/2)]

#print axioms solution

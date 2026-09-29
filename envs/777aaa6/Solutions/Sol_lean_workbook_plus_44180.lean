-- Prove2me | solution 1 for lean_workbook_plus_44180
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:23:07.403008+00:00
-- url     : https://prove2.me/submissions/987b2c51-b230-4b7c-a7a7-33c1e681e25f

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a : ℝ) : a / 2 < 0 ∨ 0 ≤ a / 2 ∧ a / 2 ≤ 2 ∨ a / 2 > 2 := by
  by_cases h0 : a/2 < 0
  · exact Or.inl h0
  by_cases h2 : a/2 ≤ 2
  · exact Or.inr (Or.inl ⟨le_of_not_gt h0,h2⟩)
  · exact Or.inr (Or.inr (lt_of_not_ge h2))

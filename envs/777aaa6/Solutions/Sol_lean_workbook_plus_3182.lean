-- Prove2me | solution 1 for lean_workbook_plus_3182
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:00:38.529703+00:00
-- url     : https://prove2.me/submissions/37872a02-8fcf-48f1-a7b6-f71ccbed8c04

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000


theorem solution (a b c : ℤ) (h₁ : a ≠ b) (h₂ : a ≠ c) (h₃ : b ≠ c) : ∃ a b, 30 ∣ a^3 * b - a * b^3 := by
  refine ⟨0, ?_⟩ <;> norm_num at *

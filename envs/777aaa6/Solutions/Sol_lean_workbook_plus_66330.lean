-- Prove2me | solution 1 for lean_workbook_plus_66330
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:55:40.948849+00:00
-- url     : https://prove2.me/submissions/e1c04cde-80f3-4f80-a4bf-369f7eb3c7fb

import Mathlib
set_option autoImplicit false

theorem solution (α₁ α₂ α₃ : ℝ) : ∃ β₁ β₂ β₃ : ℝ, β₁ + β₃ = α₁ ∧ β₁ + β₂ = α₂ ∧ β₂ + β₃ = α₃   := by
  refine' ⟨α₁ / 2 + α₂ / 2 - α₃ / 2, α₂ / 2 + α₃ / 2 - α₁ / 2, α₃ / 2 + α₁ / 2 - α₂ / 2, _, _, _⟩ <;> ring

#print axioms solution

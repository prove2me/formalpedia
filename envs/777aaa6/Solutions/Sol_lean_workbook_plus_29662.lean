-- Prove2me | solution 1 for lean_workbook_plus_29662
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T20:55:45.232349+00:00
-- url     : https://prove2.me/submissions/bc29777f-a4f0-40d5-a8b4-ac231d31664b

import Mathlib
set_option autoImplicit false

theorem solution (x y z a b c: ℝ) (h₁ : 1 ≥ x ∧ x ≥ y ∧ y ≥ z ∧ z ≥ 0)(h₂ : a = Real.sqrt (x - y) ∧ b = Real.sqrt (y - z) ∧ c = Real.sqrt (x - z))(h₃ : a^2 + b^2 = c^2): 0 ≤ c ∧ c ≤ 1   := by
  rw [h₂.2.2]
  constructor
  · exact Real.sqrt_nonneg (x - z)
  · apply (Real.sqrt_le_left (by norm_num)).2
    nlinarith only [h₁.1, h₁.2.2.2]

#print axioms solution

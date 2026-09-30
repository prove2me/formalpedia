-- Prove2me | solution 1 for lean_workbook_plus_44363
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:30:36.942379+00:00
-- url     : https://prove2.me/submissions/58be402b-6885-4906-8232-f586f1081586

import Mathlib
set_option autoImplicit false

theorem solution {a b c : ℝ} (h : a * b * c * (a ^ 2 - a * b + b ^ 2) * (b ^ 2 - b * c + c ^ 2) * (c ^ 2 - c * a + a ^ 2) = a ^ 3 * b ^ 3 * c ^ 3) : a * b * c = 0 ∨ (a ^ 2 - a * b + b ^ 2) * (b ^ 2 - b * c + c ^ 2) * (c ^ 2 - c * a + a ^ 2) = a ^ 2 * b ^ 2 * c ^ 2   := by
  by_cases hz : a * b * c = 0
  · exact Or.inl hz
  · right
    apply mul_left_cancel₀ hz
    calc
      a * b * c * ((a ^ 2 - a * b + b ^ 2) * (b ^ 2 - b * c + c ^ 2) *
          (c ^ 2 - c * a + a ^ 2)) =
          a * b * c * (a ^ 2 - a * b + b ^ 2) * (b ^ 2 - b * c + c ^ 2) *
          (c ^ 2 - c * a + a ^ 2) := by ring
      _ = a ^ 3 * b ^ 3 * c ^ 3 := h
      _ = a * b * c * (a ^ 2 * b ^ 2 * c ^ 2) := by ring

#print axioms solution

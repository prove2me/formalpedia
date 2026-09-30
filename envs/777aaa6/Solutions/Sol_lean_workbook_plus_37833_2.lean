-- Prove2me | solution 2 for lean_workbook_plus_37833
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:30:03.467624+00:00
-- url     : https://prove2.me/submissions/400d90fc-173e-4964-827d-2f59e90cebe5

import Mathlib
set_option autoImplicit false

theorem solution  (y z a : ℂ)
  (h₀ : y^2 = a)
  (h₁ : z^3 = a) :
  (y / z)^6 = a   := by
  by_cases hz : z = 0
  · have ha : a = 0 := by simpa [hz] using h₁.symm
    simp [hz, ha]
  · rw [div_pow]
    apply (div_eq_iff (pow_ne_zero 6 hz)).2
    calc
      y ^ 6 = (y ^ 2) ^ 3 := by ring
      _ = a ^ 3 := by rw [h₀]
      _ = a * (z ^ 3) ^ 2 := by rw [h₁]; ring
      _ = a * z ^ 6 := by ring

#print axioms solution

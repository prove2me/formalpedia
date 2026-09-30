-- Prove2me | solution 1 for lean_workbook_plus_50338
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T20:34:04.652494+00:00
-- url     : https://prove2.me/submissions/c7d6e505-4850-4988-a5ab-5a404be2fc6b

import Mathlib
set_option autoImplicit false

theorem solution (a b c : ℝ) : |a^3| ≤ b * c → a^6 + b^6 + c^6 ≤ b^6 + c^6 + b^2 * c^2   := by
  intro h
  have hlo : -(b * c) <= a^3 := (abs_le.mp h).1
  have hhi : a^3 <= b * c := (abs_le.mp h).2
  have hp : 0 <= (b * c - a^3) * (b * c + a^3) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith only [hp]

#print axioms solution

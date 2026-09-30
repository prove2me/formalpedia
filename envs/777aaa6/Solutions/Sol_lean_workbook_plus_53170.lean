-- Prove2me | solution 1 for lean_workbook_plus_53170
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:12:36.389199+00:00
-- url     : https://prove2.me/submissions/c28eff7a-9672-4b40-bc62-1ba4f76619fd

import Mathlib
set_option autoImplicit false

theorem solution (a b c d : ℝ) : (a+b) * (c+d) * (a+d) * (b+c) ≥ (a+b+c+d) * (a * b * c + b * c * d + c * d * a + d * a * b) ∧ (a+d) * (b+c) * (a+c) * (b+d) ≥ (a+b+c+d) * (a * b * c + b * c * d + c * d * a + d * a * b) ∧ (a+c) * (b+d) * (a+b) * (c+d) ≥ (a+b+c+d) * (a * b * c + b * c * d + c * d * a + d * a * b)   := by
  constructor
  · nlinarith only [sq_nonneg (a * c - b * d)]
  · constructor
    · nlinarith only [sq_nonneg (a * b - c * d)]
    · nlinarith only [sq_nonneg (a * d - b * c)]

#print axioms solution

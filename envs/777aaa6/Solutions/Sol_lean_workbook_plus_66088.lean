-- Prove2me | solution 1 for lean_workbook_plus_66088
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:55:39.969415+00:00
-- url     : https://prove2.me/submissions/58b399cc-6996-4f4d-9584-734266234c06

import Mathlib
set_option autoImplicit false

theorem solution  (x y : ℝ)
  (h₀ : y = x - 1)
  (h₁ : x^4 + (x - 2)^4 = 34) :
  y^4 + 6 * y^2 - 16 = 0   := by
  calc
    y ^ 4 + 6 * y ^ 2 - 16 = (x ^ 4 + (x - 2) ^ 4 - 34) / 2 := by
      rw [h₀]
      ring
    _ = 0 := by rw [h₁]; norm_num

#print axioms solution

-- Prove2me | solution 1 for lean_workbook_plus_66642
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:54:42.485838+00:00
-- url     : https://prove2.me/submissions/f0980ee4-560a-465a-86d0-aa11483d0696

import Mathlib
set_option autoImplicit false

theorem solution (a b c : ℚ) (h₁ : a = 1 / 4) (h₂ : b = 2 / 9) (h₃ : c = 1 / 2) : a * b * c = 1 / 36   := by
  simp only [h₁, h₂, h₃]
  norm_num

#print axioms solution

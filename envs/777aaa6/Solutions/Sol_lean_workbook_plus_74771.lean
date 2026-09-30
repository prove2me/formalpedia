-- Prove2me | solution 1 for lean_workbook_plus_74771
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:07:18.427764+00:00
-- url     : https://prove2.me/submissions/35098d34-6c2e-4b1a-8ee3-87df3df95fcd

import Mathlib
set_option autoImplicit false

theorem solution (x : ℝ) (hx : x ≠ 0) : (x^6 + x^3 + 1) * (x^3 - 1)^2 / x^4 ≥ 0   := by
  apply div_nonneg
  · apply mul_nonneg
    · nlinarith [sq_nonneg (x^3 + 1/2)]
    · exact sq_nonneg _
  · positivity

#print axioms solution

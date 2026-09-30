-- Prove2me | solution 1 for lean_workbook_plus_75108
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:50:10.874715+00:00
-- url     : https://prove2.me/submissions/d551eb8f-8169-4485-aae8-5af4920d9d09

import Mathlib
set_option autoImplicit false

theorem solution (x y : ℝ) (h₁ : x > 0 ∧ y > 0) (h₂ : x < y) : x - 1/x < y - 1/y   := by
  have hrec : 1 / y < 1 / x := one_div_lt_one_div_of_lt h₁.1 h₂
  linarith only [h₂, hrec]

#print axioms solution

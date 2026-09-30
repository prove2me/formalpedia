-- Prove2me | solution 1 for lean_workbook_plus_44541
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:13:21.921919+00:00
-- url     : https://prove2.me/submissions/d7fceb42-6966-4d4e-995d-90ef4aa4584b

import Mathlib
set_option autoImplicit false

theorem solution (x : ℝ) : (x - 2) * (x + 3) > 0 ↔ x < -3 ∨ x > 2   := by
  constructor
  intro h
  apply or_iff_not_imp_left.mpr
  intro hx
  nlinarith
  rintro (hx | hx) <;> nlinarith

#print axioms solution

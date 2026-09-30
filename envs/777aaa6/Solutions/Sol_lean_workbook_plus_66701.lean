-- Prove2me | solution 1 for lean_workbook_plus_66701
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:45:39.175294+00:00
-- url     : https://prove2.me/submissions/d66417cf-ae49-4d66-8d37-bae574aed16c

import Mathlib
set_option autoImplicit false

theorem solution  (x y : ℝ)
  (h₀ : 0 < x ∧ 0 < y)
  (h₁ : x / y = 2 / 5)
  (h₂ : y = 162 - 2 * x) :
  x = 36 ∧ y = 90   := by
  have he := (div_eq_iff (ne_of_gt h₀.2)).1 h₁
  constructor <;> linarith

#print axioms solution

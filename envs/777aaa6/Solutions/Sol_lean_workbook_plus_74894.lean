-- Prove2me | solution 1 for lean_workbook_plus_74894
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:07:19.772496+00:00
-- url     : https://prove2.me/submissions/bf8cdb48-3162-4fe2-ba2c-632579e9806c

import Mathlib
set_option autoImplicit false

theorem solution  (x : ℕ)
  (h₀ : 0 < x)
  (h₁ : 40 * x + 20727 ≥ 2 * (8 * x^2 + 4 * x + 3) + 1) :
  1 ≤ x ∧ x ≤ 37   := by
  apply And.intro
  linarith [h₀]
  nlinarith

#print axioms solution

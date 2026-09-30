-- Prove2me | solution 1 for lean_workbook_plus_23676
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:27:54.633348+00:00
-- url     : https://prove2.me/submissions/7aced8d9-fe9c-4fc4-8d4e-6b00c60cf084

import Mathlib
set_option autoImplicit false

theorem solution (a b : ℝ) : 4 * (a ^ 3 + b ^ 3) ≥ (a + b) ^ 3 ↔ a ^ 3 + b ^ 3 ≥ a * b ^ 2 + a ^ 2 * b   := by
  norm_num [sq]
  ring_nf
  constructor <;> intro h <;> linarith

#print axioms solution

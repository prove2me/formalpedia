-- Prove2me | solution 1 for lean_workbook_plus_65608
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:18:13.722688+00:00
-- url     : https://prove2.me/submissions/9aa4f478-4903-44f7-947c-5a516842d890

import Mathlib
set_option autoImplicit false

theorem solution (a b : ℝ) : (a + b) * (1 - a * b) / ((1 + a ^ 2) * (1 + b ^ 2)) ≤ 1 / 2 ↔ (a * b + a + b - 1) ^ 2 ≥ 0   := by
  rw [div_le_iff₀]
  field_simp
  ring_nf
  constructor <;> intro h <;> linarith [h]
  field_simp
  nlinarith

#print axioms solution

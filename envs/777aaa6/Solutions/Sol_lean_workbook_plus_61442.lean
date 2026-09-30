-- Prove2me | solution 1 for lean_workbook_plus_61442
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:55:45.965606+00:00
-- url     : https://prove2.me/submissions/39f36e55-ee7e-4007-9ded-c964cbd7985c

import Mathlib
set_option autoImplicit false

theorem solution (a b : ℝ) (hab : a > 0 ∧ b > 0) : |a - b| < max (|a|) (|b|)   := by
  rw [abs_of_pos hab.1, abs_of_pos hab.2]
  rcases le_total a b with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h), max_eq_right h]
    linarith [hab.1]
  · rw [abs_of_nonneg (sub_nonneg.mpr h), max_eq_left h]
    linarith [hab.2]

#print axioms solution

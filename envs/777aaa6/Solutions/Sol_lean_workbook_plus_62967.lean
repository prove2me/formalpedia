-- Prove2me | solution 1 for lean_workbook_plus_62967
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:10:34.811237+00:00
-- url     : https://prove2.me/submissions/05c7b395-3659-45cf-8c91-c8281e690c07

import Mathlib
set_option autoImplicit false

theorem solution (k : ℝ) : (k - 1 / 2) * (k + 2) * (k - 3) * (k + 1 / 3) = 0 ↔ k = 1 / 2 ∨ k = -2 ∨ k = 3 ∨ k = -1 / 3   := by
  simp [sub_eq_zero, add_eq_zero_iff_eq_neg, or_assoc]
  ring_nf

#print axioms solution

-- Prove2me | solution 1 for lean_workbook_plus_17256
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:50:34.91887+00:00
-- url     : https://prove2.me/submissions/5079ee1b-4e40-4bbf-a283-347de1aed520

import Mathlib
set_option autoImplicit false

theorem solution : ∀ x : ℤ, ‖2 * x - 3‖ > 9 → ‖x‖ > 2   := by
  simp (config := { contextual := true }) [Int.norm_eq_abs]
  intro x h
  contrapose! h
  rw [abs_le] at h ⊢
  constructor <;> linarith

#print axioms solution

-- Prove2me | solution 1 for lean_workbook_plus_57582
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:22:06.487607+00:00
-- url     : https://prove2.me/submissions/060cb746-fa0d-40a3-a739-e04e9c4da879

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false

theorem solution (x : ℂ) :
    x ^ 3 + 7 * x ^ 2 + 11 * x + 5 = 0 ↔ x = -1 ∨ x = -1 ∨ x = -5 := by
  have hf : x ^ 3 + 7 * x ^ 2 + 11 * x + 5 = (x + 1) * (x + 1) * (x + 5) := by
    ring
  rw [hf]
  simp only [mul_eq_zero, add_eq_zero_iff_eq_neg, or_assoc]

#print axioms solution

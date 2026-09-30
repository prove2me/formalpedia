-- Prove2me | solution 1 for lean_workbook_plus_64395
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:54:29.029059+00:00
-- url     : https://prove2.me/submissions/5079739d-ebac-459d-b58e-4fa3feb0db54

import Mathlib
set_option autoImplicit false

theorem solution (x : ℝ) : (x-20)*(x+15) = 0 ↔ x = 20 ∨ x = -15   := by
  simp [sub_eq_zero, add_eq_zero_iff_eq_neg]

#print axioms solution

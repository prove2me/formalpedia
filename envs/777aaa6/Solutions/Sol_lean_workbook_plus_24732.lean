-- Prove2me | solution 1 for lean_workbook_plus_24732
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:44:51.62363+00:00
-- url     : https://prove2.me/submissions/ac03566a-f55d-47a7-a133-da4344e25360

import Mathlib
set_option autoImplicit false

theorem solution (x y z : ℝ) (h : x + y + z = 0) : (x^5 + y^5 + z^5)/5 = (x^2 + y^2 + z^2)/2 * (x^3 + y^3 + z^3)/3 ∧ (x^7 + y^7 + z^7)/7 = (x^5 + y^5 + z^5)/5 * (x^2 + y^2 + z^2)/2   := by
  have h1 : z = -(x + y) := by linarith
  rw [h1]
  simp
  constructor <;> ring

#print axioms solution

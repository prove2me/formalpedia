-- Prove2me | solution 1 for lean_workbook_plus_70549
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:54:26.92343+00:00
-- url     : https://prove2.me/submissions/7da9925d-0ce4-46cc-b8ce-a8c8d4f10c76

import Mathlib
set_option autoImplicit false

theorem solution (a_0 a_n : ℝ) (n : ℕ) :
    a_n ≥ a_0 / (2^n) ↔ (2^n) * a_n ≥ a_0 := by
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  simpa [mul_comm] using (div_le_iff₀ hp : a_0 / (2 ^ n) ≤ a_n ↔ a_0 ≤ a_n * 2 ^ n)

#print axioms solution

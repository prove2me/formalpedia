-- Prove2me | solution 1 for lean_workbook_plus_67503
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:45:30.590224+00:00
-- url     : https://prove2.me/submissions/48fcf30e-1162-441c-b531-fd1a8ab084bc

import Mathlib
set_option autoImplicit false

theorem solution  (a b : ℝ)
  (h₀ : 0 < a ∧ 0 < b) :
  1 / (4 * a) + 1 / (4 * b) ≥ 1 / (a + b)   := by
  rcases h₀ with ⟨ha, hb⟩
  have hab : 0 < a + b := add_pos ha hb
  have hd : 0 < 4 * a * b * (a + b) := by positivity
  apply (mul_le_mul_iff_left₀ hd).mp
  field_simp [ne_of_gt ha, ne_of_gt hb, ne_of_gt hab]
  nlinarith [sq_nonneg (a - b)]

#print axioms solution

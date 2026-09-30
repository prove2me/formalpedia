-- Prove2me | solution 1 for lean_workbook_plus_44232
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:30:43.410549+00:00
-- url     : https://prove2.me/submissions/53893a99-71eb-40bc-a090-548394d571be

import Mathlib
set_option autoImplicit false

theorem solution :  ∀ a : ℝ, 1 ≤ a → (a + 1) ^ 2 / a ≥ 12 * (a ^ 2 + 2) / (a + 2) ^ 2   := by
  intro a ha
  have ha0 : 0 < a := by linarith only [ha]
  have hd : 0 < (a + 2) ^ 2 := sq_pos_of_pos (by linarith only [ha])
  apply (div_le_div_iff₀ hd ha0).2
  nlinarith only [mul_nonneg (sq_nonneg (a - 1)) (sq_nonneg (a - 2))]

#print axioms solution

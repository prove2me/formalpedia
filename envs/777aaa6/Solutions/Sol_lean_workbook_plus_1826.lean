-- Prove2me | solution 1 for lean_workbook_plus_1826
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:00:31.304059+00:00
-- url     : https://prove2.me/submissions/b9ce773a-b1c8-4b7b-a716-7769817fa638

import Mathlib
set_option autoImplicit false

theorem solution (x y : ℝ) : (|x| + |y|) ^ 2 ≥ (|x + y|) ^ 2   := by
  exact pow_le_pow_left₀ (abs_nonneg (x + y)) (abs_add_le x y) 2

#print axioms solution

-- Prove2me | solution 1 for lean_workbook_plus_65043
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T17:03:03.356192+00:00
-- url     : https://prove2.me/submissions/02370581-2c6d-4c80-9ca9-e2b34835bae3

import Mathlib
set_option autoImplicit false

theorem solution : ¬ (∀ a b c : ℝ, (a + 1) / (b ^ 2 + 1) + (b + 1) / (c ^ 2 + 1) + (c + 1) / (a ^ 2 + 1) ≤ a ^ 2 + b ^ 2 + c ^ 2) := by
  intro h
  have bad := h (1 / 2) (1 / 2) (1 / 2)
  have hp : (1 / 2 : ℝ) ^ 2 + (1 / 2) ^ 2 + (1 / 2) ^ 2 <
      (1 / 2 + 1) / ((1 / 2) ^ 2 + 1) +
      (1 / 2 + 1) / ((1 / 2) ^ 2 + 1) +
      (1 / 2 + 1) / ((1 / 2) ^ 2 + 1) := by norm_num
  exact (not_le_of_gt hp) bad

#print axioms solution

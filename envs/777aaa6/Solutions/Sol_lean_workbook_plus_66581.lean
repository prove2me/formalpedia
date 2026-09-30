-- Prove2me | solution 1 for lean_workbook_plus_66581
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T17:03:09.068891+00:00
-- url     : https://prove2.me/submissions/0fefdd81-cd47-4c6c-a356-81175960de62

import Mathlib
set_option autoImplicit false

theorem solution : ¬ (∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b + c = 3 → a * b ^ 2 * (b ^ 2 + 1) + b * c ^ 2 * (c ^ 2 + 1) + c * a ^ 2 * (a ^ 2 + 1) ≤ 6) := by
  intro h
  have bad := h 2 (1 / 2) (1 / 2) (by norm_num)
  have hp : (6 : ℝ) <
      2 * (1 / 2) ^ 2 * ((1 / 2) ^ 2 + 1) +
      (1 / 2) * (1 / 2) ^ 2 * ((1 / 2) ^ 2 + 1) +
      (1 / 2) * 2 ^ 2 * (2 ^ 2 + 1) := by norm_num
  exact (not_le_of_gt hp) bad

#print axioms solution

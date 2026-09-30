-- Prove2me | solution 1 for lean_workbook_plus_47777
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T17:18:25.341328+00:00
-- url     : https://prove2.me/submissions/4f46a917-d54a-476a-9423-9012d47c6128

import Mathlib
set_option autoImplicit false

theorem solution : ¬ (∀ x y z t : ℝ, 2 ≥ (x^2 * t^2 + x * y * z * t + y^2 * z^2) + (x^2 * z^2 + x * y * z * t + y^2 * t^2) ∧ (x^2 * t^2 + x * y * z * t + y^2 * z^2) + (x^2 * z^2 + x * y * z * t + y^2 * t^2) ≥ 3 / 4 * (x * t + y * z)^2 + 3 / 4 * (x * z + y * t)^2 ∧ 3 / 4 * (x * t + y * z)^2 + 3 / 4 * (x * z + y * t)^2 ≥ 3 / 8 * (x + y)^2 * (z + t)^2) := by
  intro h
  have bad := (h 1 1 1 1).1
  have hp : (2 : ℝ) <
      ((1 : ℝ) ^ 2 * 1 ^ 2 + 1 * 1 * 1 * 1 + 1 ^ 2 * 1 ^ 2) +
      ((1 : ℝ) ^ 2 * 1 ^ 2 + 1 * 1 * 1 * 1 + 1 ^ 2 * 1 ^ 2) := by norm_num
  exact (not_le_of_gt hp) bad

#print axioms solution

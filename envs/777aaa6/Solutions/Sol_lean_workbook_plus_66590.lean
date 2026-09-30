-- Prove2me | solution 1 for lean_workbook_plus_66590
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T16:45:42.567716+00:00
-- url     : https://prove2.me/submissions/e2f62b02-0d7a-4dea-ac6e-b1ddca25fa22

import Mathlib
set_option autoImplicit false

theorem solution : ¬ (∀ x y z : ℝ, 1 / x * 1 / y * 1 / z = 1 → 9 / 2 ≤ (1 / x + 1 / y + 1 / z) * (x + y + z) ∧ (1 / x + 1 / y + 1 / z) * (x + y + z) ≤ 3 * (1 / x * x + 1 / y * y + 1 / z * z)) := by
  intro h
  have bad := (h 2 1 (1 / 2) (by norm_num)).2
  norm_num at bad
  have hb : (49 : ℝ) / 4 ≤ 3 * (2 + 1) := bad
  have hp : (3 : ℝ) * (2 + 1) < 49 / 4 := by norm_num
  exact (not_le_of_gt hp) hb

#print axioms solution

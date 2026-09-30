-- Prove2me | solution 1 for lean_workbook_plus_66511
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T17:03:06.336616+00:00
-- url     : https://prove2.me/submissions/7326efa3-3cb2-4721-af65-aae2d1e255f9

import Mathlib
set_option autoImplicit false

theorem solution : ¬ (∀ a b c : ℝ, (1 - a) * (1 - b) * (1 - c) + (1 + a) * (1 + b) * (1 + c) ≥ 0) := by
  intro h
  have bad := h 1 (-2) 0
  have hp : (1 - (1 : ℝ)) * (1 - (-2)) * (1 - 0) +
      (1 + 1) * (1 + (-2)) * (1 + 0) < 0 := by norm_num
  exact (not_le_of_gt hp) bad

#print axioms solution

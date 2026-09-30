-- Prove2me | solution 1 for lean_workbook_plus_37958
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T17:30:18.242929+00:00
-- url     : https://prove2.me/submissions/f1d40862-1834-4192-901a-f55ed2002ff3

import Mathlib
set_option autoImplicit false

theorem solution : ¬ (∀ a b c : ℝ, 2 * (a ^ 5 + b ^ 5 + c ^ 5) ≥ a * b ^ 4 + b * c ^ 4 + c * a ^ 4 + a ^ 4 * b + b ^ 4 * c + c ^ 4 * a) := by
  intro h
  have bad := h (-1) 0 0
  norm_num at bad
  have hb : (0 : ℝ) + 0 ≤ -2 := bad
  have hp : (-2 : ℝ) < 0 + 0 := by norm_num
  exact (not_le_of_gt hp) hb

#print axioms solution

-- Prove2me | solution 1 for lean_workbook_plus_42280
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T17:30:50.095319+00:00
-- url     : https://prove2.me/submissions/87427a0a-3691-453e-967f-f2ca8e230d56

import Mathlib
set_option autoImplicit false

theorem solution : ¬ (∀ a b c : ℝ, (a + b + c)^4 ≥ 27 * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2)) := by
  intro h
  have bad := h 1 1 (1 / 2)
  norm_num at bad

#print axioms solution

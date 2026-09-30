-- Prove2me | solution 1 for lean_workbook_plus_64182
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T16:54:30.728796+00:00
-- url     : https://prove2.me/submissions/95274aaa-7437-4c2b-8f89-8514041a984b

import Mathlib
set_option autoImplicit false

theorem solution : ¬ (∀ a b c : ℝ, 2 * (a + b + c) ^ 3 ≥ 9 * (a ^ 2 + b ^ 2 + c ^ 2 + a * b + b * c + c * a)) := by
  intro h
  have bad := h (1 / 2) (1 / 2) (1 / 2)
  norm_num at bad

#print axioms solution

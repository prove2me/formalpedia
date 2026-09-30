-- Prove2me | solution 1 for lean_workbook_plus_64591
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T16:54:41.683156+00:00
-- url     : https://prove2.me/submissions/10101ff9-2625-481c-b216-448b1a018ca7

import Mathlib
set_option autoImplicit false

theorem solution : ¬ (∀ a b c : ℝ, a^2 + b^2 + c^2 ≥ a + b + c) := by
  intro h
  have bad := h (1 / 2) (1 / 2) (1 / 2)
  norm_num at bad

#print axioms solution

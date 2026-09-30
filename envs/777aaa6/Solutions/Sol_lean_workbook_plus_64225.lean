-- Prove2me | solution 1 for lean_workbook_plus_64225
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T16:54:34.827134+00:00
-- url     : https://prove2.me/submissions/b1b7fd09-ff25-4ff1-9b68-f26564cdc6e1

import Mathlib
set_option autoImplicit false

theorem solution : ¬ (∀ a b c : ℝ, (1 / (2 + b ^ 2 + c ^ 2) + 1 / (2 + c ^ 2 + a ^ 2) + 1 / (2 + a ^ 2 + b ^ 2) : ℝ) ≤ 3 / 4) := by
  intro h
  have bad := h (1 / 2) (1 / 2) (1 / 2)
  norm_num at bad

#print axioms solution

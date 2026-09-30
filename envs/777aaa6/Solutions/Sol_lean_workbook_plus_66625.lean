-- Prove2me | solution 1 for lean_workbook_plus_66625
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T16:45:38.376913+00:00
-- url     : https://prove2.me/submissions/cbecc553-f16e-44a6-acc9-1113b1b2dc6d

import Mathlib
set_option autoImplicit false

theorem solution : ¬ (∀ a b : ℝ, 2 * a ^ 3 * b ^ 3 + 2 * a * b ≥ 4 * a ^ 2 * b ^ 2) := by
  intro h
  have bad := h (-1) 1
  norm_num at bad

#print axioms solution

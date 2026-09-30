-- Prove2me | solution 1 for lean_workbook_plus_68225
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T16:45:18.337877+00:00
-- url     : https://prove2.me/submissions/e6bf9b38-4b02-470a-a985-9eb2e6796747

import Mathlib
set_option autoImplicit false

theorem solution : ¬ (∀ a b c : ℝ, a^2+b^2+c^2=1 → a^4+b^4+c^4+4*a*b*c>1) := by
  intro h
  have bad := h (1 / 3) (2 / 3) (2 / 3) (by norm_num)
  norm_num at bad

#print axioms solution

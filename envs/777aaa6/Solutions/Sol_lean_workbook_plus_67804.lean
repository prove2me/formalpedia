-- Prove2me | solution 1 for lean_workbook_plus_67804
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T16:45:25.381376+00:00
-- url     : https://prove2.me/submissions/d287e844-80c4-40e9-827b-9b64005f2c2f

import Mathlib
set_option autoImplicit false

theorem solution : ¬ (∀ p : ℕ, p > 3 ∧ p.Prime → p % 6 = 5) := by
  intro h
  have bad := h 7 (by norm_num)
  norm_num at bad

#print axioms solution

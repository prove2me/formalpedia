-- Prove2me | solution 1 for lean_workbook_plus_66477
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T17:03:07.544375+00:00
-- url     : https://prove2.me/submissions/544a4b94-4c46-4189-8229-f71e80f38b7b

import Mathlib
set_option autoImplicit false

theorem solution : ¬ (∀ x y : ℤ, x * y ^ 2 - y ^ 2 + x * y - y = x ^ 2 * y - x ^ 2 + x * y - x) := by
  intro h
  have bad := h 0 1
  norm_num at bad

#print axioms solution

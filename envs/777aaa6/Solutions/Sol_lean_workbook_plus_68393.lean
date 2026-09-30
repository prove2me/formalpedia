-- Prove2me | solution 1 for lean_workbook_plus_68393
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:45:34.035813+00:00
-- url     : https://prove2.me/submissions/2838f6ab-c2bd-45a8-97d6-69b6b810b70d

import Mathlib
set_option autoImplicit false

theorem solution (a b c : ℚ) (ha : a = (1999 * 1999 - 1999) / (1998 * 1998 + 1998)) (hb : b = (2000 * 2000 - 2000) / (1999 * 1999 + 1999)) (hc : c = (2001 * 2001 - 2001) / (2000 * 2000 + 2000)) : a * b * c = 1   := by
  rw [ha, hb, hc] at *
  norm_num

#print axioms solution

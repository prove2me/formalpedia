-- Prove2me | solution 1 for lean_workbook_plus_22580
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T19:25:47.006543+00:00
-- url     : https://prove2.me/submissions/f2c935e5-7178-4df5-bb65-975b3752ef2b

import Mathlib
set_option autoImplicit false

theorem solution : ¬ (∀ (n m : ℕ), m < n → m < (n - 1) / 2 → n.choose (m + 1) < n.choose m) := by
  intro h
  have bad := h 5 1 (by norm_num) (by norm_num)
  norm_num [Nat.choose] at bad

#print axioms solution

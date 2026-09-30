-- Prove2me | solution 1 for lean_workbook_plus_64058
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T17:03:01.747135+00:00
-- url     : https://prove2.me/submissions/f07d2a07-1c69-4989-9e73-e71f1fd9ff3b

import Mathlib
set_option autoImplicit false

theorem solution : ¬ (¬ (∃ a b c d : ℤ, a * c = d ^ 2 + 1)) := by
  intro h
  apply h
  exact ⟨1, 0, 1, 0, by norm_num⟩

#print axioms solution

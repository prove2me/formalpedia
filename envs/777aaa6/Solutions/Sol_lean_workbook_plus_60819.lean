-- Prove2me | solution 1 for lean_workbook_plus_60819
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:53:19.311677+00:00
-- url     : https://prove2.me/submissions/6a2db019-03ae-4c7b-8fc2-b457fa2a289f

import Mathlib
set_option autoImplicit false

theorem solution (n : ℕ) : (n+1)*(n+3) = 440 ↔ n = 19   := by
  apply Iff.intro
  intro h
  nlinarith
  rintro rfl
  norm_num

#print axioms solution

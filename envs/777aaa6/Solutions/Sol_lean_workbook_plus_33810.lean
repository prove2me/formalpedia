-- Prove2me | solution 1 for lean_workbook_plus_33810
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:36:05.049519+00:00
-- url     : https://prove2.me/submissions/38a21e0c-4843-4497-bbf4-e7d4548a5d38

import Mathlib
set_option autoImplicit false

theorem solution (a c : ℤ) (h1 : Odd a) (h2 : Odd c) : Even (a + c)   := by
  cases' h1 with b h1
  cases' h2 with d h2
  refine ⟨b + d + 1, ?_⟩
  omega

#print axioms solution

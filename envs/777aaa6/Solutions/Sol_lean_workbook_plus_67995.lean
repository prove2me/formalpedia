-- Prove2me | solution 1 for lean_workbook_plus_67995
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:45:23.260223+00:00
-- url     : https://prove2.me/submissions/218471a7-a8d8-482c-b984-13c220917f4c

import Mathlib
set_option autoImplicit false

theorem solution : ∃ n, Nat.Prime n ∧ n ∣ 3 ^ (n - 1) - 2 ^ (n - 1)   := by
  use 5
  exact ⟨Nat.prime_five, by norm_num⟩

#print axioms solution

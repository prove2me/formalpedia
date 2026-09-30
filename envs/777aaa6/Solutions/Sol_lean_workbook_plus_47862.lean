-- Prove2me | solution 1 for lean_workbook_plus_47862
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:18:37.107597+00:00
-- url     : https://prove2.me/submissions/e1e121f6-cbb6-4d00-86d8-f509b375aed1

import Mathlib
set_option autoImplicit false

theorem solution : ∀ n : ℤ, n^7 ≡ n [ZMOD 2]   := by
  intro n
  have hn : n % 2 = 0 ∨ n % 2 = 1 := by omega
  have hp : n ^ 7 ≡ (n % 2) ^ 7 [ZMOD 2] := (Int.mod_modEq n 2).symm.pow 7
  rcases hn with h | h <;> simpa [Int.ModEq, h] using hp

#print axioms solution

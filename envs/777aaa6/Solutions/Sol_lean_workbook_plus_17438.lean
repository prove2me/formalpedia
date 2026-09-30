-- Prove2me | solution 1 for lean_workbook_plus_17438
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:46:45.789932+00:00
-- url     : https://prove2.me/submissions/0ddd2450-f1f0-4991-bc0d-ed6abeebd3a4

import Mathlib
set_option autoImplicit false

theorem solution (m : ℤ) : m^5 - m ≡ 0 [ZMOD 5]   := by
  have hr0 : 0 ≤ m % 5 := Int.emod_nonneg m (by norm_num)
  have hr5 : m % 5 < 5 := Int.emod_lt_of_pos m (by norm_num)
  have hr : m % 5 = 0 ∨ m % 5 = 1 ∨ m % 5 = 2 ∨ m % 5 = 3 ∨ m % 5 = 4 := by omega
  have hm : m ≡ m % 5 [ZMOD 5] := (Int.mod_modEq m 5).symm
  have hp : m^5-m ≡ (m % 5)^5-m % 5 [ZMOD 5] := (hm.pow 5).sub hm
  rcases hr with h | h | h | h | h <;> simpa [Int.ModEq, h] using hp

#print axioms solution

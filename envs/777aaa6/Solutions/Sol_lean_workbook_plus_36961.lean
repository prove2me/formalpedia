-- Prove2me | solution 1 for lean_workbook_plus_36961
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:30:17.316981+00:00
-- url     : https://prove2.me/submissions/24d06c1e-b7ce-481b-a38a-46f0d4feef5e

import Mathlib
set_option autoImplicit false

theorem solution  (n : ℕ) :
  11 ∣ (25^n - 3^n)   := by
  exact (show 11 ∣ 25 - 3 by norm_num).trans (Nat.sub_dvd_pow_sub_pow 25 3 n)

#print axioms solution

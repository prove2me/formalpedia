-- Prove2me | Theorems.Thm_flt7_coprime_sum_phi7
-- name    : flt7_coprime_sum_phi7
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-12T07:35:37.080504+00:00
-- url     : https://prove2.me/theorems/16076ec4-2e64-477d-b466-d898a21f6f67
-- statement:
--   In FLT-7: (a+b)*Phi7(a,b) = c^7. Follows from the factorization a^7+b^7 = (a+b)*Phi7(a,b) and h_eq.

import Mathlib.Tactic.Ring

theorem flt7_coprime_sum_phi7 (a b c : ℤ) (h_eq : a ^ 7 + b ^ 7 = c ^ 7) (h_cop : Int.gcd a b = 1) : (a + b) * (a ^ 6 - a ^ 5 * b + a ^ 4 * b ^ 2 - a ^ 3 * b ^ 3 + a ^ 2 * b ^ 4 - a * b ^ 5 + b ^ 6) = c ^ 7 := by sorry

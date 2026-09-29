-- Prove2me | Theorems.Thm_flt13_coprime_sum_phi13
-- name    : flt13_coprime_sum_phi13
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-12T07:47:35.90494+00:00
-- url     : https://prove2.me/theorems/0486afc1-a283-4f6a-b3c1-1db17bad9626
-- statement:
--   In FLT-13: (a+b)*Phi13(a,b) = c^13.

import Mathlib.Tactic.Ring

theorem flt13_coprime_sum_phi13 (a b c : ℤ) (h_eq : a ^ 13 + b ^ 13 = c ^ 13) (h_cop : Int.gcd a b = 1) : (a + b) * (a ^ 12 - a ^ 11 * b + a ^ 10 * b ^ 2 - a ^ 9 * b ^ 3 + a ^ 8 * b ^ 4 - a ^ 7 * b ^ 5 + a ^ 6 * b ^ 6 - a ^ 5 * b ^ 7 + a ^ 4 * b ^ 8 - a ^ 3 * b ^ 9 + a ^ 2 * b ^ 10 - a * b ^ 11 + b ^ 12) = c ^ 13 := by sorry

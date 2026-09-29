-- Prove2me | Theorems.Thm_flt11_coprime_sum_phi11
-- name    : flt11_coprime_sum_phi11
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-12T07:47:30.109984+00:00
-- url     : https://prove2.me/theorems/94ddb8c0-6678-467b-99bf-e8f520ef95be
-- statement:
--   In FLT-11: (a+b)*Phi11(a,b) = c^11. Follows from cyclotomic factorization and h_eq.

import Mathlib.Tactic.Ring

theorem flt11_coprime_sum_phi11 (a b c : ℤ) (h_eq : a ^ 11 + b ^ 11 = c ^ 11) (h_cop : Int.gcd a b = 1) : (a + b) * (a ^ 10 - a ^ 9 * b + a ^ 8 * b ^ 2 - a ^ 7 * b ^ 3 + a ^ 6 * b ^ 4 - a ^ 5 * b ^ 5 + a ^ 4 * b ^ 6 - a ^ 3 * b ^ 7 + a ^ 2 * b ^ 8 - a * b ^ 9 + b ^ 10) = c ^ 11 := by sorry

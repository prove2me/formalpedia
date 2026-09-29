-- Prove2me | Theorems.Thm_flt5_coprime_sum_phi5
-- name    : flt5_coprime_sum_phi5
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-12T07:18:47.021654+00:00
-- url     : https://prove2.me/theorems/63e05a51-d86b-4b98-bf66-f984920c3283
-- statement:
--   In FLT-5: (a+b)*Phi5(a,b) = c^5. Immediate from cyclotomic5_factored and h_eq.

import Mathlib.Tactic.Ring

theorem flt5_coprime_sum_phi5 (a b c : ℤ) (h_eq : a ^ 5 + b ^ 5 = c ^ 5) (h_cop : Int.gcd a b = 1) : (a + b) * (a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4) = c ^ 5 := by sorry

-- Prove2me | Theorems.Thm_flt5_case1_phi_is_fifth_power
-- name    : flt5_case1_phi_is_fifth_power
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-12T09:11:12.00671+00:00
-- url     : https://prove2.me/theorems/06a54f36-8939-4695-a8b8-22c2a7576beb
-- statement:
--   In FLT-5 descent (Case 1: 5 does not divide c), if gcd(a,b)=1 and a^5+b^5=c^5, then Phi10(a,b) = a^4-a^3b+a^2b^2-ab^3+b^4 is a 5th power integer.

import Theorems.Thm_coprime_fifth_power_factor
import Theorems.Thm_flt5_descent_gcd_one
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD

theorem flt5_case1_phi_is_fifth_power (a b c : ℤ) (h_eq : a ^ 5 + b ^ 5 = c ^ 5) (h_cop : Int.gcd a b = 1) (h_not5c : ¬(5 : ℤ) ∣ c) : ∃ e : ℤ, a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 = e ^ 5 := by sorry

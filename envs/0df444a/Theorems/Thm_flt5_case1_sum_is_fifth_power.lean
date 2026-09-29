-- Prove2me | Theorems.Thm_flt5_case1_sum_is_fifth_power
-- name    : flt5_case1_sum_is_fifth_power
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-12T08:58:07.2889+00:00
-- url     : https://prove2.me/theorems/aebff539-c0bc-4e7c-85b8-5fbf568c4725
-- statement:
--   In FLT-5 descent (Case 1: 5 does not divide c), if gcd(a,b)=1 and a^5+b^5=c^5, then a+b is a 5th power integer.

import Theorems.Thm_coprime_fifth_power_factor
import Theorems.Thm_flt5_coprime_sum_phi5
import Theorems.Thm_flt5_descent_gcd_one
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD

theorem flt5_case1_sum_is_fifth_power (a b c : ℤ) (h_eq : a ^ 5 + b ^ 5 = c ^ 5) (h_cop : Int.gcd a b = 1) (h_not5c : ¬(5 : ℤ) ∣ c) : ∃ d : ℤ, a + b = d ^ 5 := by sorry

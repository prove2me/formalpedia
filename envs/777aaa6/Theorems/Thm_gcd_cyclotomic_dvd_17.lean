-- Prove2me | Theorems.Thm_gcd_cyclotomic_dvd_17
-- name    : gcd_cyclotomic_dvd_17
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-12T07:18:42.904442+00:00
-- url     : https://prove2.me/theorems/6833150a-5925-4478-b379-c71fea4ad764
-- statement:
--   gcd(a+b, Phi17(a,b)) divides 17 when gcd(a,b)=1.

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Ring

theorem gcd_cyclotomic_dvd_17 (a b : ℤ) (hab : Int.gcd a b = 1) : (Int.gcd (a + b) (a ^ 16 - a ^ 15 * b + a ^ 14 * b ^ 2 - a ^ 13 * b ^ 3 + a ^ 12 * b ^ 4 - a ^ 11 * b ^ 5 + a ^ 10 * b ^ 6 - a ^ 9 * b ^ 7 + a ^ 8 * b ^ 8 - a ^ 7 * b ^ 9 + a ^ 6 * b ^ 10 - a ^ 5 * b ^ 11 + a ^ 4 * b ^ 12 - a ^ 3 * b ^ 13 + a ^ 2 * b ^ 14 - a * b ^ 15 + b ^ 16) : ℤ) ∣ 17 := by sorry

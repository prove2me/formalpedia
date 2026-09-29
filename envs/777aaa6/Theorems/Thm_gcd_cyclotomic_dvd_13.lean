-- Prove2me | Theorems.Thm_gcd_cyclotomic_dvd_13
-- name    : gcd_cyclotomic_dvd_13
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-12T07:04:44.178295+00:00
-- url     : https://prove2.me/theorems/4c8fe094-6ea5-4ac1-a487-e5144eb02720
-- statement:
--   Key GCD step for FLT n=13. gcd(a+b, Phi13) divides 13 when gcd(a,b)=1.

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Ring

theorem gcd_cyclotomic_dvd_13 (a b : ℤ) (hab : Int.gcd a b = 1) : (Int.gcd (a + b) (a ^ 12 - a ^ 11 * b + a ^ 10 * b ^ 2 - a ^ 9 * b ^ 3 + a ^ 8 * b ^ 4 - a ^ 7 * b ^ 5 + a ^ 6 * b ^ 6 - a ^ 5 * b ^ 7 + a ^ 4 * b ^ 8 - a ^ 3 * b ^ 9 + a ^ 2 * b ^ 10 - a * b ^ 11 + b ^ 12) : ℤ) ∣ 13 := by sorry

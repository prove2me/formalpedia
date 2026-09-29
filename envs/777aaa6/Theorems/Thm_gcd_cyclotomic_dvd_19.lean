-- Prove2me | Theorems.Thm_gcd_cyclotomic_dvd_19
-- name    : gcd_cyclotomic_dvd_19
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-12T07:29:15.836561+00:00
-- url     : https://prove2.me/theorems/1a3d70c2-6c3b-4708-ba36-f35c29f5cd6c
-- statement:
--   gcd(a+b, Phi19(a,b)) divides 19 when gcd(a,b)=1. Uses 19*b^18 = Phi19(a,b) - (a+b)*Q19(a,b) where Q19 has degree 17 with coefficients 1,-2,...,-18.

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Ring

theorem gcd_cyclotomic_dvd_19 (a b : ℤ) (hab : Int.gcd a b = 1) : (Int.gcd (a + b) (a ^ 18 - a ^ 17 * b + a ^ 16 * b ^ 2 - a ^ 15 * b ^ 3 + a ^ 14 * b ^ 4 - a ^ 13 * b ^ 5 + a ^ 12 * b ^ 6 - a ^ 11 * b ^ 7 + a ^ 10 * b ^ 8 - a ^ 9 * b ^ 9 + a ^ 8 * b ^ 10 - a ^ 7 * b ^ 11 + a ^ 6 * b ^ 12 - a ^ 5 * b ^ 13 + a ^ 4 * b ^ 14 - a ^ 3 * b ^ 15 + a ^ 2 * b ^ 16 - a * b ^ 17 + b ^ 18) : ℤ) ∣ 19 := by sorry

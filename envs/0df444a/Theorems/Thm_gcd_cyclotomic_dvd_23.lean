-- Prove2me | Theorems.Thm_gcd_cyclotomic_dvd_23
-- name    : gcd_cyclotomic_dvd_23
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-12T07:29:21.895632+00:00
-- url     : https://prove2.me/theorems/a03d3cc3-1753-42b7-a62b-8dfbad21a7aa
-- statement:
--   gcd(a+b, Phi23(a,b)) divides 23 when gcd(a,b)=1. Uses 23*b^22 = Phi23(a,b) - (a+b)*Q23(a,b) where Q23 has degree 21 with coefficients 1,-2,...,-22.

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Ring

theorem gcd_cyclotomic_dvd_23 (a b : ℤ) (hab : Int.gcd a b = 1) : (Int.gcd (a + b) (a ^ 22 - a ^ 21 * b + a ^ 20 * b ^ 2 - a ^ 19 * b ^ 3 + a ^ 18 * b ^ 4 - a ^ 17 * b ^ 5 + a ^ 16 * b ^ 6 - a ^ 15 * b ^ 7 + a ^ 14 * b ^ 8 - a ^ 13 * b ^ 9 + a ^ 12 * b ^ 10 - a ^ 11 * b ^ 11 + a ^ 10 * b ^ 12 - a ^ 9 * b ^ 13 + a ^ 8 * b ^ 14 - a ^ 7 * b ^ 15 + a ^ 6 * b ^ 16 - a ^ 5 * b ^ 17 + a ^ 4 * b ^ 18 - a ^ 3 * b ^ 19 + a ^ 2 * b ^ 20 - a * b ^ 21 + b ^ 22) : ℤ) ∣ 23 := by sorry

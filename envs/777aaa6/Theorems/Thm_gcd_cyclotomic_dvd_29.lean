-- Prove2me | Theorems.Thm_gcd_cyclotomic_dvd_29
-- name    : gcd_cyclotomic_dvd_29
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-12T07:42:16.646628+00:00
-- url     : https://prove2.me/theorems/c20e9afe-b92f-4d62-8ae3-4f7fc752b37f
-- statement:
--   gcd(a+b, Phi29(a,b)) divides 29 when gcd(a,b)=1.

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Ring

theorem gcd_cyclotomic_dvd_29 (a b : ℤ) (hab : Int.gcd a b = 1) : (Int.gcd (a + b) (a ^ 28 - a ^ 27 * b + a ^ 26 * b ^ 2 - a ^ 25 * b ^ 3 + a ^ 24 * b ^ 4 - a ^ 23 * b ^ 5 + a ^ 22 * b ^ 6 - a ^ 21 * b ^ 7 + a ^ 20 * b ^ 8 - a ^ 19 * b ^ 9 + a ^ 18 * b ^ 10 - a ^ 17 * b ^ 11 + a ^ 16 * b ^ 12 - a ^ 15 * b ^ 13 + a ^ 14 * b ^ 14 - a ^ 13 * b ^ 15 + a ^ 12 * b ^ 16 - a ^ 11 * b ^ 17 + a ^ 10 * b ^ 18 - a ^ 9 * b ^ 19 + a ^ 8 * b ^ 20 - a ^ 7 * b ^ 21 + a ^ 6 * b ^ 22 - a ^ 5 * b ^ 23 + a ^ 4 * b ^ 24 - a ^ 3 * b ^ 25 + a ^ 2 * b ^ 26 - a * b ^ 27 + b ^ 28) : ℤ) ∣ 29 := by sorry

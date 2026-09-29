-- Prove2me | Theorems.Thm_gcd_cyclotomic_dvd_7
-- name    : gcd_cyclotomic_dvd_7
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-12T06:25:59.983805+00:00
-- url     : https://prove2.me/theorems/e6012f3b-3c36-4b93-b9cb-6a0e860613bb
-- statement:
--   **Key GCD step for FLT n=7 (Lamé's proof).** If gcd(a,b)=1 then gcd(a+b, Φ₇(a,b)) divides 7, where Φ₇(a,b) = a^6 − a^5b + a^4b^2 − a^3b^3 + a^2b^4 − ab^5 + b^6. The proof uses the ring identity 7b^6 = Φ₇(a,b) − (a+b)·(a^5−2a^4b+3a^3b^2−4a^2b^3+5ab^4−6b^5), then shows gcd(D,b)=1 and hence D|7.

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Ring

theorem gcd_cyclotomic_dvd_7 (a b : ℤ) (hab : Int.gcd a b = 1) : (Int.gcd (a + b) (a ^ 6 - a ^ 5 * b + a ^ 4 * b ^ 2 - a ^ 3 * b ^ 3 + a ^ 2 * b ^ 4 - a * b ^ 5 + b ^ 6) : ℤ) ∣ 7 := by sorry

-- Prove2me | Theorems.Thm_gcd_cyclotomic_dvd_5
-- name    : gcd_cyclotomic_dvd_5
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-12T05:43:45.507822+00:00
-- url     : https://prove2.me/theorems/79719d4a-284b-4c80-a9fc-87c6ccf7c2bb
-- statement:
--   **Key GCD step in Dirichlet's proof of FLT for n=5.** If IsCoprime a b (over ℤ), then gcd(a+b, Φ₅(a,b)) divides 5, where Φ₅(a,b) = a^4 − a^3b + a^2b^2 − ab^3 + b^4. Proof: Any prime p dividing gcd(a+b, Φ₅) satisfies p | (a+b) and p | Φ₅. Using Φ₅(a,b) − 5b^4 = (a+b)·(a^3−2a^2b+3ab^2−4b^3) (a ring identity), we get p | 5b^4. From IsCoprime(a,b) and p | (a+b), one shows p ∤ b, hence p | 5, so p = 5. Thus gcd(a+b,Φ₅) | 5.

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Ring

theorem gcd_cyclotomic_dvd_5 (a b : ℤ) (hab : Int.gcd a b = 1) : (Int.gcd (a + b) (a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4) : ℤ) ∣ 5 := by sorry

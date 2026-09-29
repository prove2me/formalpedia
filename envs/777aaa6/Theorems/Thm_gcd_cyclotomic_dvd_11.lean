-- Prove2me | Theorems.Thm_gcd_cyclotomic_dvd_11
-- name    : gcd_cyclotomic_dvd_11
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-12T06:33:32.975613+00:00
-- url     : https://prove2.me/theorems/fdfa27df-b160-433f-b335-448d85b74fbc
-- statement:
--   **Key GCD step for FLT n=11.** If gcd(a,b)=1 then gcd(a+b, Φ₁₁(a,b)) divides 11, where Φ₁₁(a,b) = a^10 − a^9b + a^8b^2 − ... + b^10 is the 11th cyclotomic polynomial. Uses ring identity: 11b^10 = Φ₁₁(a,b) − (a+b)·Q₁₁(a,b) where Q₁₁ = a^9−2a^8b+3a^7b^2−4a^6b^3+5a^5b^4−6a^4b^5+7a^3b^6−8a^2b^7+9ab^8−10b^9.

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Ring

theorem gcd_cyclotomic_dvd_11 (a b : ℤ) (hab : Int.gcd a b = 1) : (Int.gcd (a + b) (a ^ 10 - a ^ 9 * b + a ^ 8 * b ^ 2 - a ^ 7 * b ^ 3 + a ^ 6 * b ^ 4 - a ^ 5 * b ^ 5 + a ^ 4 * b ^ 6 - a ^ 3 * b ^ 7 + a ^ 2 * b ^ 8 - a * b ^ 9 + b ^ 10) : ℤ) ∣ 11 := by sorry

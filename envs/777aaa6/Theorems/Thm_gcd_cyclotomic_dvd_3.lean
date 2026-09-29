-- Prove2me | Theorems.Thm_gcd_cyclotomic_dvd_3
-- name    : gcd_cyclotomic_dvd_3
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-12T06:23:10.916806+00:00
-- url     : https://prove2.me/theorems/09dd30eb-37e1-4f2b-8db0-37184d76d5d4
-- statement:
--   **Key GCD step in Euler's proof of FLT for n=3.** If gcd(a,b) = 1, then gcd(a+b, Φ₃(a,b)) divides 3, where Φ₃(a,b) = a^2 − ab + b^2. The proof mirrors that for FLT-5: use the ring identity 3b^2 = (a^2−ab+b^2) − (a+b)·(a−2b), so D = gcd(a+b,Φ₃) divides 3b^2. From gcd(a,b)=1 one shows gcd(a+b,b)=1, hence gcd(D,b)=1, so D | 3.

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Ring

theorem gcd_cyclotomic_dvd_3 (a b : ℤ) (hab : Int.gcd a b = 1) : (Int.gcd (a + b) (a ^ 2 - a * b + b ^ 2) : ℤ) ∣ 3 := by sorry

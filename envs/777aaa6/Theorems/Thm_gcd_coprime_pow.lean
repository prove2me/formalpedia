-- Prove2me | Theorems.Thm_gcd_coprime_pow
-- name    : gcd_coprime_pow
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-12T06:11:09.790074+00:00
-- url     : https://prove2.me/theorems/cd0bab6d-01cb-4b92-b843-f6e898fe8289
-- statement:
--   **GCD of coprime powers.** If gcd(a, b) = 1 then gcd(a, b^n) = 1 for all n : ℕ. This follows from the fact that if a prime p divides both a and b^n, it must divide b (by Euclid's lemma applied n times), contradicting gcd(a,b)=1. Used in Dirichlet's FLT-5 proof to show gcd(D, b^4) = 1 from gcd(a+b, b) = 1.

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD

theorem gcd_coprime_pow (a b : ℤ) (n : ℕ) (h : Int.gcd a b = 1) : Int.gcd a (b ^ n) = 1 := by sorry

-- Prove2me | Theorems.Thm_gcd_coprime_add
-- name    : gcd_coprime_add
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-12T06:09:51.199818+00:00
-- url     : https://prove2.me/theorems/2d424544-88bb-4fa1-b475-9469a50e9527
-- statement:
--   **GCD of coprime sum.** If gcd(a, b) = 1 then gcd(a + b, b) = 1. Equivalently, adding b to a does not introduce new common factors with b. This is a fundamental lemma in elementary number theory used in Dirichlet's proof of FLT for n=5: from gcd(a,b)=1 and the key GCD identity gcd(a+b, Φ₅(a,b)) | 5, one shows gcd(a+b, b) = 1 and hence gcd(a+b, b⁴) = 1, forcing the GCD to divide 5 exactly.

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD

theorem gcd_coprime_add (a b : ℤ) (h : Int.gcd a b = 1) : Int.gcd (a + b) b = 1 := by sorry

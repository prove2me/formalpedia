-- Prove2me | Theorems.Thm_flt5_descent_arith_core_v2
-- name    : flt5_descent_arith_core_v2
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-13T09:55:51.047026+00:00
-- url     : https://prove2.me/theorems/89a74323-c2a8-4c1b-82af-b3d649fc40a6
-- statement:
--   Core arithmetic descent for FLT-5 Case 2: Given all integer FLT-5 hypotheses (a^5+b^5=c^5, gcd(a,b)=1, 5|c, c=5c1, a+b=5^4*r^5, Phi(a,b)=5*s^5, gcd(r,s)=1, r*s=c1) — without any ZZ5 or norm witness — extract integers p,q with p^5+q^5=c1^5 and gcd(p,q)=1 and p≠0 and q≠0 and 0<p*q. This is the pure arithmetic core of the FLT-5 Case 2 descent: the new triple (p,q,c1) satisfies the FLT-5 equation with |c1| < |c|/5 implied by descent.

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD

theorem flt5_descent_arith_core_v2 (a b c r s c1 : ℤ) (h_eq : a ^ 5 + b ^ 5 = c ^ 5) (h_cop : Int.gcd a b = 1) (h5c : (5 : ℤ) ∣ c) (hc : c ≠ 0) (hc1 : c = 5 * c1) (hw : a + b = 5 ^ 4 * r ^ 5) (hPhi : a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 = 5 * s ^ 5) (hcop_rs : Int.gcd r s = 1) (hrs : r * s = c1) : ∃ p q : ℤ, p ^ 5 + q ^ 5 = c1 ^ 5 ∧ Int.gcd p q = 1 ∧ p ≠ 0 ∧ q ≠ 0 ∧ 0 < p * q := by sorry

-- Prove2me | Theorems.Thm_flt5_kummer_arith_descent
-- name    : flt5_kummer_arith_descent
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-13T09:36:06.722799+00:00
-- url     : https://prove2.me/theorems/5edefe61-e308-4a50-9f29-eb25f8bc8941
-- statement:
--   Pure integer arithmetic descent for FLT-5 Case 2: Given all FLT-5 hypotheses (a^5+b^5=c^5, gcd(a,b)=1, 5|c, c=5c1, a+b=5^4*r^5, Phi(a,b)=5*s^5, gcd(r,s)=1, r*s=c1) plus an integer nd with nd^5=s^5, extract integers p,q with p^5+q^5=c1^5 and gcd(p,q)=1 and p≠0 and q≠0 and 0<p*q. This is the arithmetic Kummer descent: nd=s (by injectivity of x^5 on ℤ), and the descent arithmetic produces the new FLT-5 pair (p,q) from the factorization structure of r and s=nd. Reduces to the Dirichlet descent computation.

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD

theorem flt5_kummer_arith_descent (a b c r s c1 nd : ℤ) (h_eq : a ^ 5 + b ^ 5 = c ^ 5) (h_cop : Int.gcd a b = 1) (h5c : (5 : ℤ) ∣ c) (hc : c ≠ 0) (hc1 : c = 5 * c1) (hw : a + b = 5 ^ 4 * r ^ 5) (hPhi : a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 = 5 * s ^ 5) (hcop_rs : Int.gcd r s = 1) (hrs : r * s = c1) (hnd : nd ^ 5 = s ^ 5) : ∃ p q : ℤ, p ^ 5 + q ^ 5 = c1 ^ 5 ∧ Int.gcd p q = 1 ∧ p ≠ 0 ∧ q ≠ 0 ∧ 0 < p * q := by sorry

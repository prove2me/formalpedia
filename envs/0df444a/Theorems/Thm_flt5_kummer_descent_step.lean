-- Prove2me | Theorems.Thm_flt5_kummer_descent_step
-- name    : flt5_kummer_descent_step
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-13T08:57:24.584121+00:00
-- url     : https://prove2.me/theorems/ceba3bb3-10ee-4b80-9b03-e06b085db98e
-- statement:
--   Full Kummer descent step for FLT-5: Given all FLT-5 hypotheses (a^5+b^5=c^5, gcd(a,b)=1, 5|c, c=5c1, a+b=5^4*r^5, Phi(a,b)=5*s^5, gcd(r,s)=1, r*s=c1) plus d:ZZ5 with N(d)^5=s^5 and hPID, extract integers p,q with p^5+q^5=c1^5. The descent: N(d)=s implies d has ZZ5-coordinates giving the descent pair, and the FLT equation reduces to p^5+q^5=c1^5 with c1=r*s and the smaller solution.

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD

theorem flt5_kummer_descent_step (a b c r s c1 : ℤ) (h_eq : a ^ 5 + b ^ 5 = c ^ 5) (h_cop : Int.gcd a b = 1) (h5c : (5 : ℤ) ∣ c) (hc : c ≠ 0) (hc1 : c = 5 * c1) (hw : a + b = 5 ^ 4 * r ^ 5) (hPhi : a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 = 5 * s ^ 5) (hcop_rs : Int.gcd r s = 1) (hrs : r * s = c1) (d : NumberField.RingOfIntegers (CyclotomicField 5 ℚ)) (hd_norm : (Algebra.norm ℤ d) ^ 5 = s ^ 5) (hPID : IsPrincipalIdealRing (NumberField.RingOfIntegers (CyclotomicField 5 ℚ))) : ∃ p q : ℤ, p ^ 5 + q ^ 5 = c1 ^ 5 ∧ Int.gcd p q = 1 ∧ p ≠ 0 ∧ q ≠ 0 ∧ 0 < p * q := by sorry

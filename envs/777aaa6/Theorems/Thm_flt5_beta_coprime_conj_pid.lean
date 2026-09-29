-- Prove2me | Theorems.Thm_flt5_beta_coprime_conj_pid
-- name    : flt5_beta_coprime_conj_pid
-- status  : Disproved
-- author  : @tianyipeng
-- created : 2026-05-13T17:56:11.590595+00:00
-- url     : https://prove2.me/theorems/40694ce6-23c3-48ca-a939-95e4eda59e08
-- statement:
--   Given a, b, s : Z with gcd(a,b)=1, beta : ZZ5 = RingOfIntegers(CyclotomicField 5 Q) with Algebra.norm Z beta = s^5, and hPID : ZZ5 is a PID, for each Galois automorphism sigma : CK5 <~a[Q] CK5 with sigma != AlgEquiv.refl, IsCoprime beta ((RingOfIntegers.mapAlgEquiv sigma) beta) in ZZ5. Strategy: beta - sigma(beta) = b*(zeta - sigma(zeta)) = b * unit * lambda (since (1-zeta^k) is unit*lambda for k not 0 mod 5, proved via N(1-zeta^k)=N(lambda)=5). Any common divisor d | beta and sigma(beta) in ZZ5 divides beta - sigma(beta) = unit*lambda*b. If d|lambda then since lambda is the unique prime above 5, N(beta)=s^5 and gcd(a,b)=1 prevent both beta and sigma(beta) being divisible by lambda. If d|b then d|N(beta)=s^5 and combined gcd conditions show d is a unit.

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD

theorem flt5_beta_coprime_conj_pid (a b s : ℤ) (h_cop : Int.gcd a b = 1) (β : NumberField.RingOfIntegers (CyclotomicField 5 ℚ)) (hβ : Algebra.norm ℤ β = s ^ 5) (hPID : IsPrincipalIdealRing (NumberField.RingOfIntegers (CyclotomicField 5 ℚ))) : ∀ σ : (CyclotomicField 5 ℚ) ≃ₐ[ℚ] (CyclotomicField 5 ℚ), σ ≠ AlgEquiv.refl → IsCoprime β (NumberField.RingOfIntegers.mapAlgEquiv σ β) := by sorry

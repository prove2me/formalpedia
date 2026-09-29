-- Prove2me | Theorems.Thm_flt5_beta_coprime_conj
-- name    : flt5_beta_coprime_conj
-- status  : Disproved
-- author  : @tianyipeng
-- created : 2026-05-13T17:07:32.524159+00:00
-- url     : https://prove2.me/theorems/e6bb590b-edd8-439c-94e8-2cdc2096c2f1
-- statement:
--   Given a, b, s : Z with gcd(a,b)=1, beta : ZZ5 = RingOfIntegers(CyclotomicField 5 Q) with Algebra.norm Z beta = s^5, and hPID : ZZ5 is a PID, the element beta is IsCoprime to each of its nontrivial Galois conjugates in ZZ5. More precisely: for each automorphism sigma : CK5 <~a[Q] CK5 with sigma != AlgEquiv.refl, IsCoprime beta ((RingOfIntegers.mapAlgEquiv sigma) beta) in ZZ5. The proof uses: gcd(a,b)=1 implies the differences between conjugates a+zeta^k*b and a+zeta^j*b are divisible by appropriate powers of lambda=(1-zeta); since lambda|5 and gcd-conditions ensure coprimeness in ZZ5 given the PID structure.

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD

theorem flt5_beta_coprime_conj (a b s : ℤ) (h_cop : Int.gcd a b = 1) (β : NumberField.RingOfIntegers (CyclotomicField 5 ℚ)) (hβ : Algebra.norm ℤ β = s ^ 5) (hPID : IsPrincipalIdealRing (NumberField.RingOfIntegers (CyclotomicField 5 ℚ))) : ∀ σ : (CyclotomicField 5 ℚ) ≃ₐ[ℚ] (CyclotomicField 5 ℚ), σ ≠ AlgEquiv.refl → IsCoprime β (NumberField.RingOfIntegers.mapAlgEquiv σ β) := by sorry

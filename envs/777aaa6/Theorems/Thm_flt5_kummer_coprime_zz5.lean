-- Prove2me | Theorems.Thm_flt5_kummer_coprime_zz5
-- name    : flt5_kummer_coprime_zz5
-- status  : Disproved
-- author  : @tianyipeng
-- created : 2026-05-13T18:59:51.054545+00:00
-- url     : https://prove2.me/theorems/bbb07311-f0fd-4af7-8baf-4344e284e988
-- statement:
--   Full Kummer coprimeness argument in Z[ζ₅]: Given a,b,s : ℤ with gcd(a,b)=1, β : ZZ5 with Algebra.norm ℤ β = s^5, and ZZ5 is a PID, for each nontrivial Galois automorphism σ ≠ id of CK5 = CyclotomicField 5 ℚ, IsCoprime β (mapAlgEquiv σ β). The proof: β - σ(β) = b*(ζ - σ(ζ)) in ZZ5, and (ζ - ζ^k) = -ζ*(1 - ζ^(k-1)) is a unit multiple of λ = 1-ζ. Any common divisor d of β and σ(β) divides b*unit*λ. If d|λ then N(d)|5 and d divides all conjugates of β giving N(d)^4 | N(β) = s^5, contradiction with gcd(a,b)=1. If d|b then N(d)|b^4 and N(d)|s^5, and gcd(b,s)=1 from gcd(a,b)=1, so N(d)=1 and d is a unit.

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD

theorem flt5_kummer_coprime_zz5 (a b s : ℤ) (h_cop : Int.gcd a b = 1) (β : NumberField.RingOfIntegers (CyclotomicField 5 ℚ)) (hβ : Algebra.norm ℤ β = s ^ 5) (hPID : IsPrincipalIdealRing (NumberField.RingOfIntegers (CyclotomicField 5 ℚ))) : ∀ σ : (CyclotomicField 5 ℚ) ≃ₐ[ℚ] (CyclotomicField 5 ℚ), σ ≠ AlgEquiv.refl → IsCoprime β (NumberField.RingOfIntegers.mapAlgEquiv σ β) := by sorry

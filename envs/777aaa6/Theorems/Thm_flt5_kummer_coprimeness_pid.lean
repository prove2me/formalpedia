-- Prove2me | Theorems.Thm_flt5_kummer_coprimeness_pid
-- name    : flt5_kummer_coprimeness_pid
-- status  : Disproved
-- author  : @tianyipeng
-- created : 2026-05-13T18:52:41.793631+00:00
-- url     : https://prove2.me/theorems/299938f8-2819-4e97-8e5a-81a52946060e
-- statement:
--   Kummer coprimeness: Given a, b, s : ℤ with gcd(a,b)=1, β : ZZ5 = RingOfIntegers(CyclotomicField 5 ℚ) with Algebra.norm ℤ β = s^5, and ZZ5 is a PID, for each nontrivial Galois automorphism σ ≠ id of CK5/ℚ, IsCoprime β (RingOfIntegers.mapAlgEquiv σ β). The Kummer argument: β - σ(β) divides into b * unit * λ in ZZ5. Any common factor d of β and σ(β) divides β - σ(β), hence d | b or d | λ. Using N(β)=s^5 and gcd(a,b)=1, both cases force d to be a unit in ZZ5.

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD

theorem flt5_kummer_coprimeness_pid (a b s : ℤ) (h_cop : Int.gcd a b = 1) (β : NumberField.RingOfIntegers (CyclotomicField 5 ℚ)) (hβ : Algebra.norm ℤ β = s ^ 5) (hPID : IsPrincipalIdealRing (NumberField.RingOfIntegers (CyclotomicField 5 ℚ))) : ∀ σ : (CyclotomicField 5 ℚ) ≃ₐ[ℚ] (CyclotomicField 5 ℚ), σ ≠ AlgEquiv.refl → IsCoprime β (NumberField.RingOfIntegers.mapAlgEquiv σ β) := by sorry

-- Prove2me | Theorems.Thm_flt5_kummer_coprime_beta_form
-- name    : flt5_kummer_coprime_beta_form
-- status  : Disproved
-- author  : @tianyipeng
-- created : 2026-05-14T07:52:23.928679+00:00
-- url     : https://prove2.me/theorems/93ed2ad1-bea7-4c99-a51f-a1f16b4c6239

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD

theorem flt5_kummer_coprime_beta_form (a b : ℤ) (h_cop : Int.gcd a b = 1) (ζ : NumberField.RingOfIntegers (CyclotomicField 5 ℚ)) (hζ : IsPrimitiveRoot (ζ : CyclotomicField 5 ℚ) 5) (β : NumberField.RingOfIntegers (CyclotomicField 5 ℚ)) (hβ_form : β = ↑a + ↑b * ζ) (hPID : IsPrincipalIdealRing (NumberField.RingOfIntegers (CyclotomicField 5 ℚ))) : ∀ σ : CyclotomicField 5 ℚ ≃ₐ[ℚ] CyclotomicField 5 ℚ, σ ≠ AlgEquiv.refl → IsCoprime β (NumberField.RingOfIntegers.mapAlgEquiv σ β) := by sorry

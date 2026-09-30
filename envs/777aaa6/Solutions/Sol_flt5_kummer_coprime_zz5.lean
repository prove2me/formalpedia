-- Prove2me | solution 1 for flt5_kummer_coprime_zz5
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T07:53:41.23984+00:00
-- url     : https://prove2.me/submissions/3a7ba292-8010-4021-91b1-122ca33eeca7

import Mathlib

set_option autoImplicit false

namespace KummerCounterexample

abbrev K := CyclotomicField 5 ℚ

instance : IsCyclotomicExtension {5} ℚ K := CyclotomicField.isCyclotomicExtension 5 ℚ

instance : NumberField K := IsCyclotomicExtension.numberField {5} ℚ K

lemma exists_nonidentity : ∃ σ : K ≃ₐ[ℚ] K, σ ≠ AlgEquiv.refl := by
  classical
  letI : IsGalois ℚ K := IsCyclotomicExtension.isGalois {5} ℚ K
  letI : Fintype (K ≃ₐ[ℚ] K) := Fintype.ofFinite _
  have hcard : Nat.card (K ≃ₐ[ℚ] K) = 4 := by
    rw [IsGalois.card_aut_eq_finrank, IsCyclotomicExtension.Rat.finrank 5 K]
    exact Nat.totient_prime Nat.prime_five
  letI : Nontrivial (K ≃ₐ[ℚ] K) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by
      rw [← Nat.card_eq_fintype_card, hcard]
      decide)
  exact exists_ne AlgEquiv.refl

end KummerCounterexample

theorem solution : ¬ (∀ (a b s : ℤ), Int.gcd a b = 1 →
    ∀ β : NumberField.RingOfIntegers (CyclotomicField 5 ℚ),
      Algebra.norm ℤ β = s ^ 5 →
      IsPrincipalIdealRing (NumberField.RingOfIntegers (CyclotomicField 5 ℚ)) →
      ∀ σ : (CyclotomicField 5 ℚ) ≃ₐ[ℚ] (CyclotomicField 5 ℚ),
        σ ≠ AlgEquiv.refl →
        IsCoprime β (NumberField.RingOfIntegers.mapAlgEquiv σ β)) := by
  intro h
  obtain ⟨σ, hσ⟩ := KummerCounterexample.exists_nonidentity
  have hnorm : Algebra.norm ℤ (0 : NumberField.RingOfIntegers (CyclotomicField 5 ℚ)) =
      (0 : ℤ) ^ 5 := by
    have hc := Algebra.coe_norm_int (0 : NumberField.RingOfIntegers (CyclotomicField 5 ℚ))
    change ((Algebra.norm ℤ (0 : NumberField.RingOfIntegers (CyclotomicField 5 ℚ))) : ℚ) =
      Algebra.norm ℚ (0 : CyclotomicField 5 ℚ) at hc
    rw [Algebra.norm_zero (R := ℚ) (S := CyclotomicField 5 ℚ)] at hc
    exact_mod_cast hc
  have hc := h 1 0 0 (by norm_num) 0 hnorm
    (IsCyclotomicExtension.Rat.five_pid (CyclotomicField 5 ℚ)) σ hσ
  exact not_isCoprime_zero_zero (by simpa using hc)

#print axioms solution

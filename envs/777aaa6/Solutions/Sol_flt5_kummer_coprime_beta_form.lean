-- Prove2me | solution 1 for flt5_kummer_coprime_beta_form
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T08:11:16.588501+00:00
-- url     : https://prove2.me/submissions/0b019d55-f166-4014-a372-a02964391d55

import Mathlib

set_option autoImplicit false

section

abbrev KummerRamified.K := CyclotomicField 5 ℚ

open KummerRamified

instance : IsCyclotomicExtension {5} ℚ K := CyclotomicField.isCyclotomicExtension 5 ℚ

instance : NumberField K := IsCyclotomicExtension.numberField {5} ℚ K

lemma KummerRamified.exists_nonidentity : ∃ σ : K ≃ₐ[ℚ] K, σ ≠ AlgEquiv.refl := by
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

lemma KummerRamified.not_coprime_conjugate (ζ : K) (hζ : IsPrimitiveRoot ζ 5) (σ : K ≃ₐ[ℚ] K) :
    ¬IsCoprime (hζ.toInteger - 1)
      (NumberField.RingOfIntegers.mapAlgEquiv σ (hζ.toInteger - 1)) := by
  letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hp : Prime (hζ.toInteger - 1) := hζ.zeta_sub_one_prime'
  have ha := hζ.toInteger_isPrimitiveRoot.associated_sub_one_map_sub_one
    (NumberField.RingOfIntegers.mapAlgEquiv σ)
  intro hc
  exact hp.not_unit (hc.isUnit_of_dvd ha.dvd)

end

theorem solution : ¬ (∀ (a b : ℤ), Int.gcd a b = 1 →
    ∀ ζ : NumberField.RingOfIntegers (CyclotomicField 5 ℚ),
      IsPrimitiveRoot (ζ : CyclotomicField 5 ℚ) 5 →
      ∀ β : NumberField.RingOfIntegers (CyclotomicField 5 ℚ),
        β = ↑a + ↑b * ζ →
        IsPrincipalIdealRing (NumberField.RingOfIntegers (CyclotomicField 5 ℚ)) →
        ∀ σ : CyclotomicField 5 ℚ ≃ₐ[ℚ] CyclotomicField 5 ℚ,
          σ ≠ AlgEquiv.refl →
          IsCoprime β (NumberField.RingOfIntegers.mapAlgEquiv σ β)) := by
  intro h
  let ζ : KummerRamified.K := IsCyclotomicExtension.zeta 5 ℚ KummerRamified.K
  have hζ : IsPrimitiveRoot ζ 5 := IsCyclotomicExtension.zeta_spec 5 ℚ KummerRamified.K
  obtain ⟨σ, hσ⟩ := KummerRamified.exists_nonidentity
  have hc := h (-1) 1 (by norm_num) hζ.toInteger (by exact hζ)
    (hζ.toInteger - 1) (by simp; ring)
    (IsCyclotomicExtension.Rat.five_pid (CyclotomicField 5 ℚ)) σ hσ
  exact KummerRamified.not_coprime_conjugate ζ hζ σ hc

#print axioms solution

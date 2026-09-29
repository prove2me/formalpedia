-- Prove2me | solution 1 for AbelianCosetClassification.modCosetIndicator_extremal
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-16T20:50:19.662936+00:00
-- url     : https://prove2.me/submissions/9b2f3153-5b2c-42de-bfa0-95ca80a7d995

-- Sol generated from Bridges/AbelianCosetClassification.lean
import Mathlib
import Definitions.Def_Bridges_AbelianCosetClassification
import Definitions.Def_Bridges_CosetClassification
import Definitions.Def_Bridges_FiniteAbelianUncertainty
import Theorems.Thm_AbelianCosetClassification_card_annChar_mul_card
import Theorems.Thm_AbelianCosetClassification_gdft_modCosetIndicator
import Theorems.Thm_AbelianCosetClassification_gsupport_modCosetIndicator
import Theorems.Thm_FiniteAbelianUncertainty_mem_dsupport

/-!
# The classification of Donoho–Stark extremals over an arbitrary finite abelian group

`Catalog/Bridges/CosetClassification.lean` classified the equality case of the Donoho–Stark
uncertainty principle on `ZMod N`: an extremal is a nonzero constant times a character times the
indicator of a coset of a subgroup. That proof used the explicit cyclic characters
`stdAddChar (j * k)` throughout. *Conjecture 3* of the thread's `FUTURE_DIRECTIONS.md` asserted
that only two structural inputs are really needed — the nondegeneracy of the pairing
`G × Ĝ → ℂ` and the duality count `|ann H| · |H| = |G|` — and that the classification therefore
holds over every finite abelian group, with the Pontryagin dual `AddChar G ℂ` in place of the
second copy of `ZMod N`.

This file proves that conjecture.

## Main results

* `AbelianCosetClassification.card_annGrp_mul_card` : **duality counting.** For a subgroup `H` of
  the dual group `AddChar G ℂ`, `|ann H| · |H| = |G|`, where `ann H ⊆ G` is the set of points on
  which every character in `H` is trivial. Proved by evaluating the double character sum
  `∑_{x ∈ G} ∑_{ψ ∈ H} ψ x` in the two possible orders.
* `AbelianCosetClassification.flat_of_extremal` : **modulus rigidity.** An extremal has constant
  modulus on its support.
* `AbelianCosetClassification.norm_gdft_eq_of_extremal` : every nonzero Fourier coefficient of an
  extremal has modulus equal to the full `ℓ¹` norm of the function.
* `AbelianCosetClassification.phase_of_extremal` : **phase rigidity**, via the equality case of
  the triangle inequality (`ExtremalCosets.sum_alignment`, reused verbatim).
* `AbelianCosetClassification.extremal_orthogonality` : the orthogonality relation
  `(ψ * ψ'⁻¹) (a - a') = 1` for `a, a'` in the support and `ψ, ψ'` in the spectrum.
* `AbelianCosetClassification.extremal_support_coset` : **the classification.** The support of an
  extremal is a coset of a subgroup of `G` of order `|supp f|`.
* `AbelianCosetClassification.extremal_spectrum_coset` : dually, the spectrum is a coset of the
  annihilator subgroup of the dual group; this comes out of the same cardinality squeeze.
* `AbelianCosetClassification.extremal_eq_modulated_coset_indicator` : the closed form, a nonzero
  constant times a character times a coset indicator.
* `AbelianCosetClassification.uncertainty_strict_of_norms_ne` : the contrapositive strict
  uncertainty principle, valid over every finite abelian group.
* `AbelianCosetClassification.modCosetIndicator_extremal` : **the converse.** Every modulated
  coset indicator is an extremal, proved from the dual duality count
  `card_annChar_mul_card`; hence `extremal_iff_modCosetIndicator`, an exact characterisation of
  the equality case, and `uncertainty_strict_of_not_modCosetIndicator`, the strict inequality for
  everything else.
* `AbelianCosetClassification.zmod_six_extremal` : a concrete instance over `ZMod 6` (the
  subgroup `{0, 3}`), certifying that the hypotheses are satisfiable.
* `AbelianCosetClassification.annGrp_annChar_eq`, `annChar_annGrp_eq`, `annihilator_antiIso` :
  the double annihilator theorem in both directions, i.e. annihilation is an inclusion-reversing
  bijection between the subgroups of `G` and those of its dual — finite Pontryagin duality at
  the level of subgroup lattices.
* `AbelianCosetClassification.extremal_additive_subgroup_order` : the additive uncertainty
  functional of an extremal is `d + |G|/d` for a subgroup order `d`.

Unlike the cyclic proof, no arithmetic of `ZMod N` is used: the only inputs are
`AddChar.sum_apply_eq_ite` (nondegeneracy of the pairing in the group variable) and
`AddChar.sum_eq_zero_of_ne_one` (nondegeneracy in the character variable).
-/

open Finset FiniteAbelianUncertainty

open AbelianCosetClassification

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-! ## 1. Annihilators and duality counting -/













/-! ## 2. The equality analysis of the Donoho–Stark chain -/










/-! ## 3. Phase rigidity and the orthogonality relation -/




/-! ## 4. The classification -/






/-! ## 5. The converse: every modulated coset indicator is an extremal -/










/-! ## 6. A concrete instance: the subgroup `{0, 3}` of `ZMod 6` -/


/-! ## 7. The annihilator Galois connection is an anti-isomorphism of subgroup lattices -/










open AbelianCosetClassification in
theorem solution{K : Finset G} (h0 : (0 : G) ∈ K)
    (hadd : ∀ x ∈ K, ∀ y ∈ K, x + y ∈ K) (a₀ : G) (psi₀ : AddChar G ℂ) {c : ℂ} (hc : c ≠ 0) :
    (gsupport (modCosetIndicator K a₀ psi₀ c)).card *
        (dsupport (gdft (modCosetIndicator K a₀ psi₀ c))).card = Fintype.card G := by
  classical
  have hKpos : (K.card : ℂ) ≠ 0 := by
    have : 0 < K.card := Finset.card_pos.2 ⟨0, h0⟩
    exact_mod_cast this.ne'
  have hunit : ∀ (chi : AddChar G ℂ) (a : G), chi a ≠ 0 := by
    intro chi a h
    have h1 : ‖chi a‖ = 1 := AddChar.norm_apply _ _
    rw [h] at h1
    simp at h1
  -- the support is the coset, of size `|K|`
  have hs : (gsupport (modCosetIndicator K a₀ psi₀ c)).card = K.card := by
    rw [gsupport_modCosetIndicator hc, Finset.card_image_of_injective _ (add_right_injective a₀)]
  -- the spectrum is the coset `ψ₀ · (ann K)⁻¹`, of size `|ann K|`
  have hspec : dsupport (gdft (modCosetIndicator K a₀ psi₀ c))
      = (annChar K).image (fun chi => psi₀ * chi⁻¹) := by
    ext psi
    rw [mem_dsupport, gdft_modCosetIndicator hadd hc]
    simp only [Finset.mem_image]
    constructor
    · intro h
      by_cases hmem : psi₀ * psi⁻¹ ∈ annChar K
      · refine ⟨psi₀ * psi⁻¹, hmem, ?_⟩
        rw [mul_inv, inv_inv, ← mul_assoc, mul_comm psi₀ psi₀⁻¹, inv_mul_cancel, one_mul]
      · rw [if_neg hmem, mul_zero] at h
        exact absurd rfl h
    · rintro ⟨chi, hchi, rfl⟩
      have hmem : psi₀ * (psi₀ * chi⁻¹)⁻¹ ∈ annChar K := by
        have : psi₀ * (psi₀ * chi⁻¹)⁻¹ = chi := by
          rw [mul_inv, inv_inv, ← mul_assoc, mul_comm psi₀ psi₀⁻¹, inv_mul_cancel, one_mul]
        rwa [this]
      rw [if_pos hmem]
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero hc (hunit _ _)) (hunit _ _)) hKpos
  have ht : (dsupport (gdft (modCosetIndicator K a₀ psi₀ c))).card = (annChar K).card := by
    rw [hspec, Finset.card_image_of_injective]
    intro x y hxy
    have : x⁻¹ = y⁻¹ := mul_left_cancel hxy
    simpa using this
  rw [hs, ht, Nat.mul_comm]
  exact card_annChar_mul_card h0 hadd

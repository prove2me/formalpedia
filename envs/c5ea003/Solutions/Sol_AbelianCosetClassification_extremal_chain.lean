-- Prove2me | solution 1 for AbelianCosetClassification.extremal_chain
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-16T20:39:06.667435+00:00
-- url     : https://prove2.me/submissions/d6c9e1e6-9848-4d48-aba8-4309abcbda98

-- Sol generated from Bridges/AbelianCosetClassification.lean
import Mathlib
import Definitions.Def_Bridges_AbelianCosetClassification
import Definitions.Def_Bridges_CosetClassification
import Definitions.Def_Bridges_FiniteAbelianUncertainty
import Theorems.Thm_FiniteAbelianUncertainty_gdft_inversion
import Theorems.Thm_FiniteAbelianUncertainty_mem_dsupport
import Theorems.Thm_FiniteAbelianUncertainty_mem_gsupport

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

omit [DecidableEq G] in
/-- The Fourier transform as a sum over the support. -/
theorem gdft_sum_gsupport (f : G → ℂ) (psi : AddChar G ℂ) :
    gdft f psi = ∑ a ∈ gsupport f, psi (-a) * f a := by
  classical
  rw [gdft]
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro x _ hx
  have : f x = 0 := by
    by_contra h
    exact hx (mem_gsupport.2 h)
  simp [this]

omit [DecidableEq G] in
/-- Every Fourier coefficient is bounded by the `ℓ¹` norm of the function. -/
theorem norm_gdft_le_sum (f : G → ℂ) (psi : AddChar G ℂ) :
    ‖gdft f psi‖ ≤ ∑ a ∈ gsupport f, ‖f a‖ := by
  classical
  rw [gdft_sum_gsupport]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  rw [norm_mul, AddChar.norm_apply, one_mul]

omit [AddCommGroup G] [Fintype G] [DecidableEq G] in
/-- The maximum of `‖f‖` is positive when `f ≠ 0`. -/
theorem max_norm_pos {f : G → ℂ} (hf : f ≠ 0) {b : G} (hb : ∀ a, ‖f a‖ ≤ ‖f b‖) :
    0 < ‖f b‖ := by
  rcases lt_or_eq_of_le (norm_nonneg (f b)) with h | h
  · exact h
  · exact absurd (funext fun a => by
      have : ‖f a‖ ≤ 0 := by linarith [hb a]
      simpa using le_antisymm this (norm_nonneg _)) hf







/-! ## 3. Phase rigidity and the orthogonality relation -/




/-! ## 4. The classification -/






/-! ## 5. The converse: every modulated coset indicator is an extremal -/










/-! ## 6. A concrete instance: the subgroup `{0, 3}` of `ZMod 6` -/


/-! ## 7. The annihilator Galois connection is an anti-isomorphism of subgroup lattices -/










open AbelianCosetClassification in
theorem solution{f : G → ℂ} (hf : f ≠ 0) {b : G} (hb : ∀ a, ‖f a‖ ≤ ‖f b‖)
    (hext : (gsupport f).card * (dsupport (gdft f)).card = Fintype.card G) :
    (∑ a ∈ gsupport f, ‖f a‖) = (gsupport f).card * ‖f b‖ ∧
      ∀ psi ∈ dsupport (gdft f), ‖gdft f psi‖ = ∑ a ∈ gsupport f, ‖f a‖ := by
  classical
  set M : ℝ := ‖f b‖ with hM
  set s : ℕ := (gsupport f).card with hs
  set t : ℕ := (dsupport (gdft f)).card with ht
  set S : ℝ := ∑ a ∈ gsupport f, ‖f a‖ with hS
  have hMpos : 0 < M := max_norm_pos hf hb
  -- the upper bound `‖f‖₁ ≤ s · M`
  have hSupper : S ≤ (s : ℝ) * M := by
    have := Finset.sum_le_card_nsmul (gsupport f) (fun a => ‖f a‖) M fun a _ => hb a
    simpa [hS, hs, nsmul_eq_mul] using this
  -- the lower bound coming from inversion
  have hA : ‖∑ psi : AddChar G ℂ, psi b * gdft f psi‖ = (Fintype.card G : ℝ) * M := by
    rw [gdft_inversion f b, norm_mul, hM]
    simp
  have hB : ‖∑ psi : AddChar G ℂ, psi b * gdft f psi‖
      ≤ ∑ psi ∈ dsupport (gdft f), ‖gdft f psi‖ := by
    have hrestrict : ∑ psi : AddChar G ℂ, psi b * gdft f psi
        = ∑ psi ∈ dsupport (gdft f), psi b * gdft f psi := by
      refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
      intro psi _ hpsi
      have : gdft f psi = 0 := by
        by_contra h
        exact hpsi (mem_dsupport.2 h)
      simp [this]
    rw [hrestrict]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun psi _ => ?_))
    rw [norm_mul, AddChar.norm_apply, one_mul]
  have hC : ∑ psi ∈ dsupport (gdft f), ‖gdft f psi‖ ≤ (t : ℝ) * S := by
    have := Finset.sum_le_card_nsmul (dsupport (gdft f)) (fun psi => ‖gdft f psi‖) S
      fun psi _ => norm_gdft_le_sum f psi
    simpa [ht, nsmul_eq_mul] using this
  have hst : (t : ℝ) * (s : ℝ) = (Fintype.card G : ℝ) := by
    have hcast : (s * t : ℕ) = Fintype.card G := hext
    push_cast [← hcast]; ring
  have hGM : (Fintype.card G : ℝ) * M ≤ (t : ℝ) * S := by
    rw [← hA]; exact hB.trans hC
  have htpos : (0 : ℝ) < t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · exfalso
      rw [h] at hGM
      simp only [Nat.cast_zero, zero_mul] at hGM
      have hGpos : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
      nlinarith
    · exact_mod_cast h
  -- the `ℓ¹` norm is exactly `s · M`
  have hSeq : S = (s : ℝ) * M := by
    have h4 : (t : ℝ) * ((s : ℝ) * M) ≤ (t : ℝ) * S := by
      calc (t : ℝ) * ((s : ℝ) * M) = ((t : ℝ) * (s : ℝ)) * M := by ring
        _ = (Fintype.card G : ℝ) * M := by rw [hst]
        _ ≤ (t : ℝ) * S := hGM
    have := le_of_mul_le_mul_left h4 htpos
    linarith
  refine ⟨hSeq, ?_⟩
  -- the spectral coefficients all have the maximal modulus
  have hsum : ∑ psi ∈ dsupport (gdft f), ‖gdft f psi‖ = ∑ _psi ∈ dsupport (gdft f), S := by
    have hge : (t : ℝ) * S ≤ ∑ psi ∈ dsupport (gdft f), ‖gdft f psi‖ := by
      refine le_trans (le_of_eq ?_) (hA ▸ hB)
      calc (t : ℝ) * S = ((t : ℝ) * (s : ℝ)) * M := by rw [hSeq]; ring
        _ = (Fintype.card G : ℝ) * M := by rw [hst]
    have hconst : ∑ _psi ∈ dsupport (gdft f), S = (t : ℝ) * S := by
      rw [Finset.sum_const, nsmul_eq_mul, ht]
    rw [hconst]
    exact le_antisymm hC hge
  exact fun psi hpsi =>
    (Finset.sum_eq_sum_iff_of_le fun psi _ => norm_gdft_le_sum f psi).1 hsum psi hpsi

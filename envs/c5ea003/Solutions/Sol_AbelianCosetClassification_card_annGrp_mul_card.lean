-- Prove2me | solution 1 for AbelianCosetClassification.card_annGrp_mul_card
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-16T20:39:01.785309+00:00
-- url     : https://prove2.me/submissions/46d07ae3-79b1-425b-90a6-c5e2a3818232

-- Sol generated from Bridges/AbelianCosetClassification.lean
import Mathlib
import Definitions.Def_Bridges_AbelianCosetClassification
import Definitions.Def_Bridges_CosetClassification
import Definitions.Def_Bridges_FiniteAbelianUncertainty
import Theorems.Thm_AbelianCosetClassification_sum_subgroup_apply

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









omit [DecidableEq G] in
/-- The sum of a character over the whole group: `|G|` for the trivial character, `0` otherwise.
This is nondegeneracy of the pairing in the character variable. -/
theorem sum_char_univ (psi : AddChar G ℂ) :
    ∑ x : G, psi x = if psi = 1 then (Fintype.card G : ℂ) else 0 := by
  classical
  by_cases h : psi = 1
  · subst h
    simp
  · simp [h, AddChar.sum_eq_zero_of_ne_one h]




/-! ## 2. The equality analysis of the Donoho–Stark chain -/










/-! ## 3. Phase rigidity and the orthogonality relation -/




/-! ## 4. The classification -/






/-! ## 5. The converse: every modulated coset indicator is an extremal -/










/-! ## 6. A concrete instance: the subgroup `{0, 3}` of `ZMod 6` -/


/-! ## 7. The annihilator Galois connection is an anti-isomorphism of subgroup lattices -/










open AbelianCosetClassification in
theorem solution{H : Finset (AddChar G ℂ)} (h1 : (1 : AddChar G ℂ) ∈ H)
    (hmul : ∀ a ∈ H, ∀ b ∈ H, a * b ∈ H) :
    (annGrp H).card * H.card = Fintype.card G := by
  classical
  have key : ((annGrp H).card * H.card : ℂ) = (Fintype.card G : ℂ) := by
    have hswap : ∑ x : G, ∑ psi ∈ H, psi x = ∑ psi ∈ H, ∑ x : G, psi x := Finset.sum_comm
    have hleft : ∑ x : G, ∑ psi ∈ H, psi x = ((annGrp H).card * H.card : ℂ) := by
      rw [Finset.sum_congr rfl fun x _ => sum_subgroup_apply hmul x, Finset.sum_ite_mem]
      simp [Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
    have hright : ∑ psi ∈ H, ∑ x : G, psi x = (Fintype.card G : ℂ) := by
      rw [Finset.sum_congr rfl fun psi _ => sum_char_univ psi,
        Finset.sum_ite_eq' H (1 : AddChar G ℂ) (fun _ => (Fintype.card G : ℂ)), if_pos h1]
    rw [← hleft, hswap, hright]
  exact_mod_cast key

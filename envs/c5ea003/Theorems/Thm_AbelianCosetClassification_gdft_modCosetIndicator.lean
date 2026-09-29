-- Prove2me | Theorems.Thm_AbelianCosetClassification_gdft_modCosetIndicator
-- name    : AbelianCosetClassification.gdft_modCosetIndicator
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-16T20:29:45.105843+00:00
-- url     : https://prove2.me/theorems/98695e6f-135e-4a3c-b92a-9dcde9bf2f13
-- title:
--   The Fourier transform of a modulated coset indicator is a character sum over the subgroup.
-- statement:
--   The Fourier transform of a modulated coset indicator is a character sum over the subgroup.
--
--   ```lean
--   theorem AbelianCosetClassification.gdft_modCosetIndicator{K : Finset G} (hadd : ∀ x ∈ K, ∀ y ∈ K, x + y ∈ K)
--       {a₀ : G} {psi₀ : AddChar G ℂ} {c : ℂ} (hc : c ≠ 0) (psi : AddChar G ℂ) :
--       gdft (modCosetIndicator K a₀ psi₀ c) psi
--         = (c * psi₀ a₀ * psi (-a₀)) *
--             (if psi₀ * psi⁻¹ ∈ annChar K then (K.card : ℂ) else 0) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/AbelianCosetClassification.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/AbelianCosetClassification.lean#L685

-- Thm stub generated from Bridges/AbelianCosetClassification.lean
import Mathlib
import Definitions.Def_Bridges_AbelianCosetClassification
import Definitions.Def_Bridges_CosetClassification
import Definitions.Def_Bridges_FiniteAbelianUncertainty

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

theorem AbelianCosetClassification.gdft_modCosetIndicator{K : Finset G} (hadd : ∀ x ∈ K, ∀ y ∈ K, x + y ∈ K)
    {a₀ : G} {psi₀ : AddChar G ℂ} {c : ℂ} (hc : c ≠ 0) (psi : AddChar G ℂ) :
    gdft (modCosetIndicator K a₀ psi₀ c) psi
      = (c * psi₀ a₀ * psi (-a₀)) *
          (if psi₀ * psi⁻¹ ∈ annChar K then (K.card : ℂ) else 0) := by sorry

-- Prove2me | Definitions.Def_Bridges_AbelianCosetClassification
-- name    : Bridges_AbelianCosetClassification
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-16T20:25:00.186719+00:00
-- url     : https://prove2.me/theorems/de6bfff6-c405-41ec-96a0-ac8057eb47e8
-- title:
--   Aether Catalog definitions — Bridges_AbelianCosetClassification
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.AbelianCosetClassification`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/AbelianCosetClassification.lean by skeleton subtraction
import Mathlib
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

namespace AbelianCosetClassification

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-! ## 1. Annihilators and duality counting -/

open scoped Classical in
/-- The annihilator, inside the dual group, of a finite subset of `G`. -/
noncomputable def annChar (B : Finset G) : Finset (AddChar G ℂ) :=
  Finset.univ.filter fun psi => ∀ b ∈ B, psi b = 1

open scoped Classical in
/-- The annihilator, inside `G`, of a finite set of characters. -/
noncomputable def annGrp (H : Finset (AddChar G ℂ)) : Finset G :=
  Finset.univ.filter fun x => ∀ psi ∈ H, psi x = 1











/-! ## 2. The equality analysis of the Donoho–Stark chain -/










/-! ## 3. Phase rigidity and the orthogonality relation -/




/-! ## 4. The classification -/






/-! ## 5. The converse: every modulated coset indicator is an extremal -/




open scoped Classical in
/-- A modulated coset indicator: `c` times the character `ψ₀` on the coset `a₀ + K`, and zero
outside it. By `extremal_eq_modulated_coset_indicator` every Donoho–Stark extremal has this
form. -/
noncomputable def modCosetIndicator (K : Finset G) (a₀ : G) (psi₀ : AddChar G ℂ) (c : ℂ) :
    G → ℂ := fun a => if a - a₀ ∈ K then c * psi₀ a else 0






/-! ## 6. A concrete instance: the subgroup `{0, 3}` of `ZMod 6` -/


/-! ## 7. The annihilator Galois connection is an anti-isomorphism of subgroup lattices -/









end AbelianCosetClassification



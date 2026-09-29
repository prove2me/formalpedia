-- Prove2me | solution 1 for AbelianCosetClassification.extremal_support_and_spectrum_coset
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-16T20:44:57.939432+00:00
-- url     : https://prove2.me/submissions/8b712459-0dc4-4c0f-9837-285057acd649

-- Sol generated from Bridges/AbelianCosetClassification.lean
import Mathlib
import Definitions.Def_Bridges_AbelianCosetClassification
import Definitions.Def_Bridges_CosetClassification
import Definitions.Def_Bridges_FiniteAbelianUncertainty
import Theorems.Thm_AbelianCosetClassification_card_annGrp_mul_card
import Theorems.Thm_AbelianCosetClassification_dsupport_nonempty
import Theorems.Thm_AbelianCosetClassification_extremal_orthogonality
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



open scoped Classical in
@[simp]
theorem mem_annChar {B : Finset G} {psi : AddChar G ℂ} :
    psi ∈ annChar B ↔ ∀ b ∈ B, psi b = 1 := by simp [annChar]

open scoped Classical in
omit [DecidableEq G] in
@[simp]
theorem mem_annGrp {H : Finset (AddChar G ℂ)} {x : G} :
    x ∈ annGrp H ↔ ∀ psi ∈ H, psi x = 1 := by simp [annGrp]

theorem one_mem_annChar (B : Finset G) : (1 : AddChar G ℂ) ∈ annChar B := by
  simp

theorem mul_mem_annChar {B : Finset G} {psi phi : AddChar G ℂ}
    (hpsi : psi ∈ annChar B) (hphi : phi ∈ annChar B) : psi * phi ∈ annChar B := by
  rw [mem_annChar] at *
  intro b hb
  rw [AddChar.mul_apply, hpsi b hb, hphi b hb, one_mul]

omit [DecidableEq G] in
theorem zero_mem_annGrp (H : Finset (AddChar G ℂ)) : (0 : G) ∈ annGrp H := by
  simp

omit [DecidableEq G] in
theorem add_mem_annGrp {H : Finset (AddChar G ℂ)} {x y : G}
    (hx : x ∈ annGrp H) (hy : y ∈ annGrp H) : x + y ∈ annGrp H := by
  rw [mem_annGrp] at *
  intro psi hpsi
  rw [AddChar.map_add_eq_mul, hx psi hpsi, hy psi hpsi, one_mul]





/-! ## 2. The equality analysis of the Donoho–Stark chain -/





omit [AddCommGroup G] [DecidableEq G] in
/-- The support of a nonzero function is nonempty. -/
theorem gsupport_nonempty {f : G → ℂ} (hf : f ≠ 0) : (gsupport f).Nonempty := by
  classical
  rcases Function.ne_iff.1 hf with ⟨a, ha⟩
  exact ⟨a, mem_gsupport.2 (by simpa using ha)⟩





/-! ## 3. Phase rigidity and the orthogonality relation -/




/-! ## 4. The classification -/






/-! ## 5. The converse: every modulated coset indicator is an extremal -/










/-! ## 6. A concrete instance: the subgroup `{0, 3}` of `ZMod 6` -/


/-! ## 7. The annihilator Galois connection is an anti-isomorphism of subgroup lattices -/










open AbelianCosetClassification in
theorem solution{f : G → ℂ} (hf : f ≠ 0)
    (hext : (gsupport f).card * (dsupport (gdft f)).card = Fintype.card G) :
    ∃ (K : Finset G) (H : Finset (AddChar G ℂ)) (a₀ : G) (psi₀ : AddChar G ℂ),
      (0 : G) ∈ K ∧ (∀ x ∈ K, ∀ y ∈ K, x + y ∈ K) ∧
      (1 : AddChar G ℂ) ∈ H ∧ (∀ x ∈ H, ∀ y ∈ H, x * y ∈ H) ∧
      K.card = (gsupport f).card ∧ H.card = (dsupport (gdft f)).card ∧
      gsupport f = K.image (fun x => a₀ + x) ∧
      dsupport (gdft f) = H.image (fun x => psi₀ * x) ∧
      psi₀ ∈ dsupport (gdft f) ∧ a₀ ∈ gsupport f := by
  classical
  obtain ⟨a₀, ha₀⟩ := gsupport_nonempty hf
  obtain ⟨psi₀, hpsi₀⟩ := dsupport_nonempty hf
  set B : Finset G := (gsupport f).image (fun a => a - a₀) with hB
  set C : Finset (AddChar G ℂ) := (dsupport (gdft f)).image (fun psi => psi * psi₀⁻¹) with hC
  set H : Finset (AddChar G ℂ) := annChar B with hH
  set K : Finset G := annGrp H with hK
  have h1H : (1 : AddChar G ℂ) ∈ H := one_mem_annChar B
  have hmulH : ∀ x ∈ H, ∀ y ∈ H, x * y ∈ H := fun x hx y hy => mul_mem_annChar hx hy
  -- orthogonality puts the spectrum quotients in `H`
  have hCH : C ⊆ H := by
    intro chi hchi
    rw [hC, Finset.mem_image] at hchi
    obtain ⟨psi, hpsi, rfl⟩ := hchi
    rw [hH, mem_annChar]
    intro b hb
    rw [hB, Finset.mem_image] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    exact extremal_orthogonality hf hext ha ha₀ hpsi hpsi₀
  -- `B` sits inside the double annihilator `K`
  have hBK : B ⊆ K := by
    intro b hb
    rw [hK, mem_annGrp]
    intro chi hchi
    rw [hH, mem_annChar] at hchi
    exact hchi b hb
  have hcount : K.card * H.card = Fintype.card G := card_annGrp_mul_card h1H hmulH
  have hsB : B.card = (gsupport f).card := by
    rw [hB, Finset.card_image_of_injective _ (fun x y h => by
      simpa using sub_left_injective h)]
  have htC : C.card = (dsupport (gdft f)).card := by
    rw [hC, Finset.card_image_of_injective _ (mul_left_injective psi₀⁻¹)]
  have hsK : B.card ≤ K.card := Finset.card_le_card hBK
  have htH : C.card ≤ H.card := Finset.card_le_card hCH
  have hprod : B.card * C.card = Fintype.card G := by rw [hsB, htC]; exact hext
  have hCpos : 0 < C.card :=
    Finset.card_pos.2 ⟨1, by
      rw [hC, Finset.mem_image]
      exact ⟨psi₀, hpsi₀, mul_inv_cancel psi₀⟩⟩
  have hKpos : 0 < K.card := Finset.card_pos.2 ⟨0, zero_mem_annGrp H⟩
  have hHC : H.card = C.card := by
    have h1 : K.card * H.card ≤ K.card * C.card := by
      calc K.card * H.card = B.card * C.card := hcount.trans hprod.symm
        _ ≤ K.card * C.card := Nat.mul_le_mul_right _ hsK
    have h2 : K.card * C.card ≤ K.card * H.card := Nat.mul_le_mul_left _ htH
    exact Nat.eq_of_mul_eq_mul_left hKpos (le_antisymm h1 h2)
  have hBeqK : B.card = K.card := by
    refine Nat.eq_of_mul_eq_mul_right hCpos ?_
    rw [hprod, ← hHC]
    exact hcount.symm
  have hBK' : B = K := Finset.eq_of_subset_of_card_le hBK (le_of_eq hBeqK.symm)
  have hCH' : C = H := Finset.eq_of_subset_of_card_le hCH (le_of_eq hHC)
  refine ⟨K, H, a₀, psi₀, zero_mem_annGrp H, fun x hx y hy => add_mem_annGrp hx hy,
    h1H, hmulH, by rw [← hBeqK, hsB], by rw [← hCH', htC], ?_, ?_, hpsi₀, ha₀⟩
  · ext a
    simp only [Finset.mem_image]
    constructor
    · intro ha
      refine ⟨a - a₀, ?_, by abel⟩
      rw [← hBK', hB, Finset.mem_image]
      exact ⟨a, ha, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      rw [← hBK', hB, Finset.mem_image] at hx
      obtain ⟨a, ha, rfl⟩ := hx
      simpa using ha
  · ext psi
    simp only [Finset.mem_image]
    constructor
    · intro hpsi
      refine ⟨psi * psi₀⁻¹, ?_, by rw [mul_comm psi psi₀⁻¹, mul_inv_cancel_left]⟩
      rw [← hCH', hC, Finset.mem_image]
      exact ⟨psi, hpsi, rfl⟩
    · rintro ⟨chi, hchi, rfl⟩
      rw [← hCH', hC, Finset.mem_image] at hchi
      obtain ⟨psi, hpsi, rfl⟩ := hchi
      have : psi₀ * (psi * psi₀⁻¹) = psi := by
        rw [mul_comm psi psi₀⁻¹, mul_inv_cancel_left]
      rwa [this]

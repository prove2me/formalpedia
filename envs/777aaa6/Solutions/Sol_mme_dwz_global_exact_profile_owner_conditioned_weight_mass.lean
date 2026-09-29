-- Prove2me | solution 1 for mme_dwz_global_exact_profile_owner_conditioned_weight_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-28T00:04:54.935204+00:00
-- url     : https://prove2.me/submissions/74529e32-5f15-432b-a5b7-ca264f4a15d8

import Theorems.Thm_mme_dwz_global_exact_profile_claim6_8_bad_weight_bound
import Theorems.Thm_mme_dwz_asymmetric_hash_retaining_states_broken_copy_mass
import Theorems.Thm_mme_dwz_table2_useful_block_typical_and_compatible
import Theorems.Thm_mme_lower_half_ZMod_image_card
import Definitions.Def_mme_dwz_table2_affine_hash_bucket

open scoped BigOperators

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

/-!
# Aggregate Claim-6.8 mass for one exact-profile owner

This is the ownerwise quantitative input to the common-state selector.  It
keeps the conditioned hash as a function of the weight word, so the affine
offset chosen by a retaining state is irrelevant.
-/

theorem solution
    (m : ℕ) (hm : 0 < m)
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p) (hlevel : 4 < p)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2))
    (retained : Fin (MME.DWZTable2Counts.scale * m) → Fin 15)
    (hretained : ∀ s,
      Fintype.card
          {t : Fin (MME.DWZTable2Counts.scale * m) // retained t = s} =
        MME.DWZTable2Counts.component s * m) :
    let L := MME.DWZTable2Counts.scale * m
    let n := L - 1
    let reindex : Fin (n + 1) ≃ Fin L := finCongr (by
      dsimp only [n, L]
      exact Nat.sub_add_cancel
        (Nat.one_le_iff_ne_zero.mpr
          (Nat.mul_ne_zero (by decide) (Nat.ne_of_gt hm))))
    let ExactProfile : (Fin L → Fin 15) → Prop := fun w ↦
      ∀ s, Fintype.card {t : Fin L // w t = s} =
        MME.DWZTable2Counts.component s * m
    let T : Finset (Fin L → Fin 15) := by
      classical
      exact Finset.univ.filter ExactProfile
    let sameZ : (Fin L → Fin 15) → Prop := fun w ↦
      ∀ t, MME.DWZSquare.shapeZ (w t) =
        MME.DWZSquare.shapeZ (retained t)
    let Outer := {w : Fin L → Fin 15 // w ∈ T ∧ sameZ w}
    let grade : MME.DWZTable2StandardForm.UsefulBlock m retained →
        Fin L → Fin (3 * 3) := fun z t ↦
      MME.DWZStep1Support.fineSplitGrade (z.1 t).1 (z.1 t).2
    let compatible : MME.DWZTable2StandardForm.UsefulBlock m retained →
        Outer → Prop := fun z A ↦
      MME.DWZStep2Source.retainedFineCompatible m
        (fun w : Fin L → Fin 15 ↦ w) (grade z) A.1
    let addressX : Outer → Fin (n + 1) → Fin 5 := fun A t ↦
      MME.DWZSquare.shapeX (A.1 (reindex t))
    let addressZ : Fin (n + 1) → Fin 5 := fun t ↦
      MME.DWZSquare.shapeZ (retained (reindex t))
    let b0 : ZMod p := 0
    let hX : (Fin (n + 1) → ZMod p) →
        (Fin (n + 1) → Fin 5) → ZMod p := fun w X ↦
      b0 + ∑ t, ((X t).val : ZMod p) * w t
    let hZ : ZMod p → (Fin (n + 1) → ZMod p) →
        (Fin (n + 1) → Fin 5) → ZMod p := fun w0 w Z ↦
      b0 + (2 : ZMod p)⁻¹ *
        (w0 + ∑ t, ((4 : ZMod p) - (Z t).val) * w t)
    let conditionedW0 : (Fin (n + 1) → ZMod p) → ZMod p := fun w ↦
      2 * (∑ t,
        (((MME.DWZSquare.shapeX (retained (reindex t))).val : ℕ) :
          ZMod p) * w t) -
        ∑ t, ((4 : ZMod p) - (addressZ t).val) * w t
    let hashRetained : Outer → (Fin (n + 1) → ZMod p) → Prop :=
      fun A w ↦ hX w (addressX A) =
        hZ (conditionedW0 w) w addressZ
    let retainedOuter : Outer := by
      refine ⟨retained, ?_, fun _ ↦ rfl⟩
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and,
        ExactProfile]
      exact hretained
    let weightCopy : (Fin (n + 1) → ZMod p) →
        MME.DWZSquare.BrokenBlockCopy
          (MME.DWZTable2StandardForm.UsefulBlock m retained) := by
      classical
      exact fun w ↦ MME.DWZStep2.brokenCopy
        (fun z A ↦ compatible z A ∧ hashRetained A w)
        (fun _ _ ↦ True) retainedOuter
    let castS : Finset (ZMod p) :=
      S.image (fun a : ℕ ↦ (a : ZMod p))
    let candidates : MME.DWZTable2StandardForm.UsefulBlock m retained →
        Finset (Fin L → Fin 15) := fun z ↦ by
      classical
      exact T.filter (fun w ↦ sameZ w ∧
        MME.DWZStep2Source.retainedFineCompatible m
          (fun w : Fin L → Fin 15 ↦ w) (grade z) w)
    (∀ z, 8 * (candidates z).card ≤ p) →
      7 * S.card * p ^ (n + 1) *
          Fintype.card
            (MME.DWZTable2StandardForm.UsefulBlock m retained) ≤
        8 * ∑ q ∈ MME.dwzAsymmetricAffineStatesRetaining
            (4 : ZMod p) castS
            (MME.dwzTable2CastX (fun t ↦ retained (reindex t)))
            (MME.dwzTable2CastY (fun t ↦ retained (reindex t)))
            (MME.dwzTable2CastZ (fun t ↦ retained (reindex t))),
          (weightCopy (fun t ↦ q.1 t.castSucc)).nonholes.card := by
  classical
  dsimp only
  intro hbudget
  let L := MME.DWZTable2Counts.scale * m
  let n := L - 1
  let reindex : Fin (n + 1) ≃ Fin L := finCongr (by
    dsimp only [n, L]
    exact Nat.sub_add_cancel
      (Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (by decide) (Nat.ne_of_gt hm))))
  let ExactProfile : (Fin L → Fin 15) → Prop := fun w ↦
    ∀ s, Fintype.card {t : Fin L // w t = s} =
      MME.DWZTable2Counts.component s * m
  let T : Finset (Fin L → Fin 15) := Finset.univ.filter ExactProfile
  let sameZ : (Fin L → Fin 15) → Prop := fun w ↦
    ∀ t, MME.DWZSquare.shapeZ (w t) =
      MME.DWZSquare.shapeZ (retained t)
  let Outer := {w : Fin L → Fin 15 // w ∈ T ∧ sameZ w}
  let grade : MME.DWZTable2StandardForm.UsefulBlock m retained →
      Fin L → Fin (3 * 3) := fun z t ↦
    MME.DWZStep1Support.fineSplitGrade (z.1 t).1 (z.1 t).2
  let compatible : MME.DWZTable2StandardForm.UsefulBlock m retained →
      Outer → Prop := fun z A ↦
    MME.DWZStep2Source.retainedFineCompatible m
      (fun w : Fin L → Fin 15 ↦ w) (grade z) A.1
  let addressX : Outer → Fin (n + 1) → Fin 5 := fun A t ↦
    MME.DWZSquare.shapeX (A.1 (reindex t))
  let addressZ : Fin (n + 1) → Fin 5 := fun t ↦
    MME.DWZSquare.shapeZ (retained (reindex t))
  let b0 : ZMod p := 0
  let hX : (Fin (n + 1) → ZMod p) →
      (Fin (n + 1) → Fin 5) → ZMod p := fun w X ↦
    b0 + ∑ t, ((X t).val : ZMod p) * w t
  let hZ : ZMod p → (Fin (n + 1) → ZMod p) →
      (Fin (n + 1) → Fin 5) → ZMod p := fun w0 w Z ↦
    b0 + (2 : ZMod p)⁻¹ *
      (w0 + ∑ t, ((4 : ZMod p) - (Z t).val) * w t)
  let conditionedW0 : (Fin (n + 1) → ZMod p) → ZMod p := fun w ↦
    2 * (∑ t,
      (((MME.DWZSquare.shapeX (retained (reindex t))).val : ℕ) :
        ZMod p) * w t) -
      ∑ t, ((4 : ZMod p) - (addressZ t).val) * w t
  let hashRetained : Outer → (Fin (n + 1) → ZMod p) → Prop :=
    fun A w ↦ hX w (addressX A) =
      hZ (conditionedW0 w) w addressZ
  let retainedOuter : Outer := by
    refine ⟨retained, ?_, fun _ ↦ rfl⟩
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and,
      ExactProfile]
    exact hretained
  let weightCopy : (Fin (n + 1) → ZMod p) →
      MME.DWZSquare.BrokenBlockCopy
        (MME.DWZTable2StandardForm.UsefulBlock m retained) := fun w ↦
    MME.DWZStep2.brokenCopy
      (fun z A ↦ compatible z A ∧ hashRetained A w)
      (fun _ _ ↦ True) retainedOuter
  let castS : Finset (ZMod p) :=
    S.image (fun a : ℕ ↦ (a : ZMod p))
  have hcastCard : castS.card = S.card :=
    mme_lower_half_ZMod_image_card p S hSrange
  have hsupport : ∀ t,
      MME.dwzTable2CastX (p := p)
          (fun t ↦ retained (reindex t)) t +
        MME.dwzTable2CastY (fun t ↦ retained (reindex t)) t +
        MME.dwzTable2CastZ (fun t ↦ retained (reindex t)) t =
      (4 : ZMod p) := by
    intro t
    have hs := MME.DWZSquare.shape_sum (retained (reindex t))
    have hc := congrArg (fun x : ℕ ↦ (x : ZMod p)) hs
    simpa only [MME.dwzTable2CastX, MME.dwzTable2CastY,
      MME.dwzTable2CastZ, Nat.cast_add, Nat.cast_ofNat] using hc
  have hCompatible :
      ∀ z : MME.DWZTable2StandardForm.UsefulBlock m retained,
        compatible z retainedOuter := by
    intro z
    have hsmallData :=
      mme_dwz_table2_useful_block_typical_and_compatible m retained z
    simp only [compatible, retainedOuter]
    simpa only [grade, MME.DWZStep2Source.retainedFineCompatible,
      MME.DWZStep1Support.fineSplitLeft_encode] using hsmallData.2
  have hHash : ∀ w : Fin (n + 1) → ZMod p,
      hashRetained retainedOuter w := by
    intro w
    dsimp only [hashRetained, retainedOuter, hX, hZ, b0, addressX,
      addressZ, conditionedW0]
    have hunit : IsUnit (2 : ZMod p) :=
      (ZMod.isUnit_iff_coprime 2 p).2 hpodd.coprime_two_left
    have hinv : (2 : ZMod p)⁻¹ * 2 = 1 :=
      ZMod.inv_mul_of_unit 2 hunit
    rw [sub_add_cancel, ← mul_assoc, hinv, one_mul]
  have hpointwise :
      ∀ z : MME.DWZTable2StandardForm.UsefulBlock m retained,
        8 * (Finset.univ.filter (fun w : Fin (n + 1) → ZMod p ↦
          1 < (Finset.univ.filter (fun A : Outer ↦
            compatible z A ∧ hashRetained A w)).card)).card ≤
          Fintype.card (Fin (n + 1) → ZMod p) := by
    intro z
    have hz := mme_dwz_global_exact_profile_claim6_8_bad_weight_bound
      m hm hpodd hlevel retained hretained z (0 : ZMod p)
    simpa only [L, n, reindex, ExactProfile, T, sameZ, Outer, grade,
      compatible, addressX, addressZ, b0, hX, hZ, conditionedW0,
      hashRetained] using hz (hbudget z)
  have hmass :=
    mme_dwz_asymmetric_hash_retaining_states_broken_copy_mass
      hpodd (4 : ZMod p) castS
      (MME.dwzTable2CastX (fun t ↦ retained (reindex t)))
      (MME.dwzTable2CastY (fun t ↦ retained (reindex t)))
      (MME.dwzTable2CastZ (fun t ↦ retained (reindex t)))
      hsupport compatible (fun _ _ ↦ True) hashRetained retainedOuter
      (fun q ↦ weightCopy (fun t ↦ q.1 t.castSucc))
      (fun _ _ ↦ rfl) (fun _ ↦ trivial) hCompatible hHash hpointwise
  simpa only [hcastCard] using hmass


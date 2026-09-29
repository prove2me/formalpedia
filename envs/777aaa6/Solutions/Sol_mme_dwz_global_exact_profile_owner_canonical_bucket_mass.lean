-- Prove2me | solution 1 for mme_dwz_global_exact_profile_owner_canonical_bucket_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-28T07:40:12.28743+00:00
-- url     : https://prove2.me/submissions/b9fbc4c2-336d-4ffb-935a-0fa90610209f

import Theorems.Thm_mme_dwz_global_exact_profile_owner_conditioned_weight_mass
import Theorems.Thm_mme_dwz_table2_affine_hash_bucket_mem_iff_retains
import Definitions.Def_mme_dwz_global_ambient_conditioned_broken_copy

open MME BigOperators

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (m : ℕ) (hm : 0 < m)
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p) (hp4 : 4 < p)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ))
    (A : Finset
      (Fin ((MME.DWZTable2Counts.scale * m - 1) + 1) → Fin 15))
    (a : Fin ((MME.DWZTable2Counts.scale * m - 1) + 1) → Fin 15)
    (haA : a ∈ A)
    (hprofile : ∀ s,
      Fintype.card
          {t : Fin ((MME.DWZTable2Counts.scale * m - 1) + 1) //
            a t = s} =
        MME.DWZTable2Counts.component s * m) :
    let L := MME.DWZTable2Counts.scale * m
    let n := L - 1
    let reindex : Fin (n + 1) ≃ Fin L := finCongr (by
      dsimp only [n, L]
      exact Nat.sub_add_cancel
        (Nat.one_le_iff_ne_zero.mpr
          (Nat.mul_ne_zero (by decide) (Nat.ne_of_gt hm))))
    let retained : Fin L → Fin 15 := fun t ↦ a (reindex.symm t)
    let ExactProfile : (Fin L → Fin 15) → Prop := fun w ↦
      ∀ s, Fintype.card {t : Fin L // w t = s} =
        MME.DWZTable2Counts.component s * m
    let T : Finset (Fin L → Fin 15) := by
      classical
      exact Finset.univ.filter ExactProfile
    let grade : MME.DWZTable2StandardForm.UsefulBlock m retained →
        Fin L → Fin (3 * 3) := fun z t ↦
      MME.DWZStep1Support.fineSplitGrade (z.1 t).1 (z.1 t).2
    let candidates : MME.DWZTable2StandardForm.UsefulBlock m retained →
        Finset (Fin L → Fin 15) := fun z ↦ by
      classical
      exact T.filter (fun w : Fin L → Fin 15 ↦
        (∀ t, MME.DWZSquare.shapeZ (w t) =
          MME.DWZSquare.shapeZ (retained t)) ∧
        MME.DWZStep2Source.retainedFineCompatible m
          (fun w : Fin L → Fin 15 ↦ w) (grade z) w)
    let hretainedT : retained ∈ T := by
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and,
        ExactProfile]
      intro s
      let E : {t : Fin L // retained t = s} ≃
          {t : Fin (n + 1) // a t = s} :=
        reindex.symm.subtypeEquiv (fun _ ↦ Iff.rfl)
      calc
        Fintype.card {t : Fin L // retained t = s} =
            Fintype.card {t : Fin (n + 1) // a t = s} :=
          Fintype.card_congr E
        _ = MME.DWZTable2Counts.component s * m := hprofile s
    (∀ z, 8 * (candidates z).card ≤ p) →
      7 * S.card * p ^ (n + 1) *
          Fintype.card
            (MME.DWZTable2StandardForm.UsefulBlock m retained) ≤
        8 * ∑ q ∈ (Finset.univ.filter (fun q :
            (Fin (n + 2) → ZMod p) × ZMod p ↦
          a ∈ MME.dwzTable2AffineHashBucket S A q)),
          (MME.DWZGlobalCorrelated.ambientConditionedBrokenCopy
            m reindex T retained hretainedT
            (fun t ↦ q.1 t.castSucc)).nonholes.card := by
  classical
  dsimp only
  let L := MME.DWZTable2Counts.scale * m
  let n := L - 1
  let reindex : Fin (n + 1) ≃ Fin L := finCongr (by
    dsimp only [n, L]
    exact Nat.sub_add_cancel
      (Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (by decide) (Nat.ne_of_gt hm))))
  let retained : Fin L → Fin 15 := fun t ↦ a (reindex.symm t)
  let ExactProfile : (Fin L → Fin 15) → Prop := fun w ↦
    ∀ s, Fintype.card {t : Fin L // w t = s} =
      MME.DWZTable2Counts.component s * m
  let T : Finset (Fin L → Fin 15) :=
    Finset.univ.filter ExactProfile
  let grade : MME.DWZTable2StandardForm.UsefulBlock m retained →
      Fin L → Fin (3 * 3) := fun z t ↦
    MME.DWZStep1Support.fineSplitGrade (z.1 t).1 (z.1 t).2
  let candidates : MME.DWZTable2StandardForm.UsefulBlock m retained →
      Finset (Fin L → Fin 15) := fun z ↦
    T.filter (fun w : Fin L → Fin 15 ↦
      (∀ t, MME.DWZSquare.shapeZ (w t) =
        MME.DWZSquare.shapeZ (retained t)) ∧
      MME.DWZStep2Source.retainedFineCompatible m
        (fun w : Fin L → Fin 15 ↦ w) (grade z) w)
  intro hbudget
  have hretained : ∀ s,
      Fintype.card {t : Fin L // retained t = s} =
        MME.DWZTable2Counts.component s * m := by
    intro s
    let E : {t : Fin L // retained t = s} ≃
        {t : Fin (n + 1) // a t = s} :=
      reindex.symm.subtypeEquiv (fun _ ↦ Iff.rfl)
    calc
      Fintype.card {t : Fin L // retained t = s} =
          Fintype.card {t : Fin (n + 1) // a t = s} :=
        Fintype.card_congr E
      _ = MME.DWZTable2Counts.component s * m := hprofile s
  have hretainedT : retained ∈ T := by
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and,
      ExactProfile]
    exact hretained
  let castS : Finset (ZMod p) :=
    S.image (fun x : ℕ ↦ (x : ZMod p))
  have hsets :
      Finset.univ.filter (fun q :
          (Fin (n + 2) → ZMod p) × ZMod p ↦
        a ∈ MME.dwzTable2AffineHashBucket S A q) =
        MME.dwzAsymmetricAffineStatesRetaining (4 : ZMod p) castS
          (MME.dwzTable2CastX a) (MME.dwzTable2CastY a)
          (MME.dwzTable2CastZ a) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      MME.dwzAsymmetricAffineStatesRetaining]
    exact mme_dwz_table2_affine_hash_bucket_mem_iff_retains
      hpodd S hSrange hSfree A a haA q
  have howner :=
    mme_dwz_global_exact_profile_owner_conditioned_weight_mass
      m hm hpodd hp4 S hSrange retained hretained hbudget
  rw [hsets]
  simpa only [L, n, reindex, retained, ExactProfile, T, grade, candidates,
    castS, MME.DWZGlobalCorrelated.ambientConditionedBrokenCopy,
    Equiv.symm_apply_apply, zero_add] using howner


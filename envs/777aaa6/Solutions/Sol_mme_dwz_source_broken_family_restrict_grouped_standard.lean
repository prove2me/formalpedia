-- Prove2me | solution 1 for mme_dwz_source_broken_family_restrict_grouped_standard
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T14:15:41.343173+00:00
-- url     : https://prove2.me/submissions/98f7e52a-42da-41f4-a9b8-091aeb839dc8

import Definitions.Def_mme_dwz_source_aligned_broken_obj
import Theorems.Thm_mme_dwz_grouped_seven_eighths_restrict_standard
import Theorems.Thm_mme_tensor_family_direct_sum_restrict_of_mixed_maps
import Theorems.Thm_mme_bigAdd_mono_restrict
import Theorems.Thm_mme_dwz_source_aligned_address_word_survives_iff_exists_nonhole
import Theorems.Thm_mme_dwz_source_aligned_broken_address_projection_certificate

open MME PiTensorProduct

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K]
    (S : TensorObj K 3) {k m N : ℕ}
    (outer : Fin k → Fin N → Fin 15)
    (copy : ∀ j : Fin k, DWZSquare.BrokenBlockCopy
      (DWZTable2StandardForm.UsefulBlock m (outer j)))
    (standardCopy : Fin k → DWZSquare.BrokenBlockCopy
      (DWZComponentRestriction.DWZStandardBlock m))
    (f : ∀ j : Fin k, ∀ i : Fin 3, S.V i →ₗ[K]
      (DWZSourceAligned.brokenAddressObj K m (outer j) (copy j)).V i)
    (hDiagonal : ∀ j : Fin k,
      PiTensorProduct.map (f j) S.t =
        (DWZSourceAligned.brokenAddressObj K m
          (outer j) (copy j)).t)
    (hMixedZero : ∀ js : Fin 3 → Fin k,
      (∀ j : Fin k, js ≠ fun _ ↦ j) →
      PiTensorProduct.map (fun i ↦ f (js i) i) S.t = 0)
    (hGrouped :
      let D : DWZComponentRestriction.DWZStandardLabelledData K m :=
        { X := TensorObj.kronFin 15
            (fun r : Fin 15 ↦
              DWZComponentRestriction.restrictedComponentPower K r m)
          basis := TensorObj.kronFinModePiBasis 15
            (fun r : Fin 15 ↦
              DWZComponentRestriction.restrictedComponentPower K r m) 2
            (fun r ↦
              DWZComponentRestriction.restrictedComponentZBasis K r m)
          label := DWZComponentRestriction.groupedUsefulBlock m }
      let G : Fin k → D.X.TypeGrading 2 := fun j ↦
        D.X.basisZAllowedGrading D.basis
          (fun W ↦ D.label W ∈ (standardCopy j).nonholes)
      ∀ j : Fin k, TensorObj.Restrict
        ((G j).blockSubtensor (fun _ ↦ 0))
        (DWZSourceAligned.brokenAddressObj K m
          (outer j) (copy j))) :
    let D : DWZComponentRestriction.DWZStandardLabelledData K m :=
      { X := TensorObj.kronFin 15
          (fun r : Fin 15 ↦
            DWZComponentRestriction.restrictedComponentPower K r m)
        basis := TensorObj.kronFinModePiBasis 15
          (fun r : Fin 15 ↦
            DWZComponentRestriction.restrictedComponentPower K r m) 2
          (fun r ↦
            DWZComponentRestriction.restrictedComponentZBasis K r m)
        label := DWZComponentRestriction.groupedUsefulBlock m }
    let G : Fin k → D.X.TypeGrading 2 := fun j ↦
      D.X.basisZAllowedGrading D.basis
        (fun W ↦ D.label W ∈ (standardCopy j).nonholes)
    (∀ (j : Fin k) (W : DWZSourceAligned.AddressZWord (outer j)),
      DWZSourceAligned.addressWordSurvives m (outer j) (copy j) W ↔
        ∃ small : DWZTable2StandardForm.UsefulBlock m (outer j),
          small ∈ (copy j).nonholes ∧
            small.1 = DWZSourceAligned.addressFineZ W) ∧
    (∀ j : Fin k,
      TensorObj.Restrict
        (DWZSourceAligned.brokenAddressObj K m (outer j) (copy j))
        (DWZSourceAligned.coarseAddressObj K (outer j))) ∧
    TensorObj.Restrict
      (TensorObj.bigAdd (fun j ↦
        (G j).blockSubtensor (fun _ ↦ 0))) S := by
  dsimp only at hGrouped ⊢
  refine ⟨?_, ?_, ?_⟩
  · intro j W
    exact mme_dwz_source_aligned_address_word_survives_iff_exists_nonhole
      m (outer j) (copy j) W
  · intro j
    exact (mme_dwz_source_aligned_broken_address_projection_certificate
      K m (outer j) (copy j)).1
  · let sourceBroken : Fin k → TensorObj K 3 := fun j ↦
      DWZSourceAligned.brokenAddressObj K m (outer j) (copy j)
    have hSource : TensorObj.Restrict (TensorObj.bigAdd sourceBroken) S :=
      mme_tensor_family_direct_sum_restrict_of_mixed_maps
        S sourceBroken f hDiagonal hMixedZero
    have hRegrouped := mme_bigAdd_mono_restrict hGrouped
    exact TensorObj.Restrict.trans hRegrouped hSource

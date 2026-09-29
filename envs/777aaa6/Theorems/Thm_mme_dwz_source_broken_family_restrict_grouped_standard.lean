-- Prove2me | Theorems.Thm_mme_dwz_source_broken_family_restrict_grouped_standard
-- name    : mme_dwz_source_broken_family_restrict_grouped_standard
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T14:15:30.246216+00:00
-- url     : https://prove2.me/theorems/f351f166-d931-49b0-9db3-c228a3523c14
-- title:
--   Source-aligned broken owners assemble into grouped Table-2 standard copies
-- statement:
--   For each retained owner, let its source-aligned broken tensor keep the complete $X$ and $Y$ spaces of the corresponding coarse CW-square address and retain exactly the canonical $Z$-basis words labelled by literal useful nonholes. Assume mode maps from one source tensor $S$ realize every such owner tensor on the diagonal and annihilate $S$ whenever the three modes select a nonconstant tuple of owners. Assume also that each owner tensor restricts, through label-aligned regrouping, to the literal grouped Table-2 broken standard copy used by the hole lemma. Then the direct sum of all grouped broken standard copies is a restriction of $S$. The theorem simultaneously records that the source $Z$ mask is exactly literal nonhole membership and that every source-aligned broken owner is a genuine $Z$-only restriction of its coarse address. Thus the only remaining source obligations are mixed-owner annihilation and grouped-coordinate transport; no additional hash premise is assumed.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definitions 5.4--5.5, Definition 6.3, Claim 6.8, and Additional Zeroing-Out Step 2; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_source_aligned_broken_obj
import Theorems.Thm_mme_dwz_grouped_seven_eighths_restrict_standard
import Theorems.Thm_mme_tensor_family_direct_sum_restrict_of_mixed_maps
import Theorems.Thm_mme_bigAdd_mono_restrict
import Theorems.Thm_mme_dwz_source_aligned_address_word_survives_iff_exists_nonhole
import Theorems.Thm_mme_dwz_source_aligned_broken_address_projection_certificate

open MME PiTensorProduct

universe u

set_option autoImplicit false

theorem mme_dwz_source_broken_family_restrict_grouped_standard
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
  sorry

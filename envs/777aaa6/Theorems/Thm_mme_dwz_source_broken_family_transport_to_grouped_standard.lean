-- Prove2me | Theorems.Thm_mme_dwz_source_broken_family_transport_to_grouped_standard
-- name    : mme_dwz_source_broken_family_transport_to_grouped_standard
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T09:54:03.118321+00:00
-- url     : https://prove2.me/theorems/c4cbf06b-e57e-43f6-ae3a-6694b5322451
-- title:
--   A literal source broken family transports to grouped Table-2 standard masks
-- statement:
--   Let a common tensor restrict to a literal direct sum of source-order broken Table-2 owners. Assume every owner has the exact Table-2 component histogram at positive scale. Then each owner can be transported to the canonical grouped Table-2 block type without changing its number of nonholes, and the common tensor restricts to the direct sum of the corresponding literal grouped restricted-component masks. Thus all cross-owner zeroing is isolated in the single source-family restriction premise.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 5.5, Lemma 5.6, Table 2, and Sections 6.2--6.3; https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_dwz_source_broken_owner_restrict_grouped_standard
import Theorems.Thm_mme_bigAdd_mono_restrict

open MME Module

universe u

set_option autoImplicit false

theorem mme_dwz_source_broken_family_transport_to_grouped_standard
    {K : Type u} [Field K]
    (S : TensorObj K 3) {k m N : ℕ}
    (outer : Fin k → Fin N → Fin 15)
    (houter : ∀ j : Fin k, ∀ s : Fin 15,
      Fintype.card {r : Fin N // outer j r = s} =
        DWZTable2Counts.component s * m)
    (hm : 0 < m)
    (copy : ∀ j : Fin k, DWZSquare.BrokenBlockCopy
      (DWZTable2StandardForm.UsefulBlock m (outer j)))
    (hSource : TensorObj.Restrict
      (TensorObj.bigAdd (fun j ↦
        DWZSourceAligned.brokenAddressObj K m (outer j) (copy j))) S) :
    ∃ standardCopy : Fin k → DWZSquare.BrokenBlockCopy
        (DWZComponentRestriction.DWZStandardBlock m),
      (∀ j : Fin k,
        (standardCopy j).nonholes.card = (copy j).nonholes.card) ∧
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
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j ↦
          (G j).blockSubtensor (fun _ ↦ 0))) S := by
  sorry

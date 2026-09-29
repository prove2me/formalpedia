-- Prove2me | Theorems.Thm_mme_dwz_source_broken_family_to_grouped_standard_of_mixed_maps
-- name    : mme_dwz_source_broken_family_to_grouped_standard_of_mixed_maps
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T09:57:10.379361+00:00
-- url     : https://prove2.me/theorems/b487b055-17a2-4ecb-988b-95861f1dc231
-- title:
--   Mixed-owner zeroing assembles grouped Table-2 broken copies
-- statement:
--   Let a common order-three tensor map to a family of source-order broken Table-2 owners. Suppose the three mode maps with one common owner recover that owner exactly, while every nonconstant choice of owners across the three modes annihilates the source tensor. If each owner has the exact Table-2 histogram at positive scale, then the source restricts to a direct sum of canonical grouped broken-standard masks, with every transported copy retaining exactly the same number of nonholes. This isolates the remaining asymmetric-hashing argument as the mixed-owner annihilation law.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 5.5, Lemma 5.6, Table 2, and Sections 6.2--6.3; https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_dwz_source_broken_owner_restrict_grouped_standard
import Theorems.Thm_mme_dwz_source_broken_family_restrict_grouped_standard

open MME Module PiTensorProduct

universe u

set_option autoImplicit false

theorem mme_dwz_source_broken_family_to_grouped_standard_of_mixed_maps
    {K : Type u} [Field K]
    (S : TensorObj K 3) {k m N : ℕ}
    (outer : Fin k → Fin N → Fin 15)
    (houter : ∀ j : Fin k, ∀ s : Fin 15,
      Fintype.card {r : Fin N // outer j r = s} =
        DWZTable2Counts.component s * m)
    (hm : 0 < m)
    (copy : ∀ j : Fin k, DWZSquare.BrokenBlockCopy
      (DWZTable2StandardForm.UsefulBlock m (outer j)))
    (f : ∀ j : Fin k, ∀ i : Fin 3, S.V i →ₗ[K]
      (DWZSourceAligned.brokenAddressObj K m
        (outer j) (copy j)).V i)
    (hDiagonal : ∀ j : Fin k,
      PiTensorProduct.map (f j) S.t =
        (DWZSourceAligned.brokenAddressObj K m
          (outer j) (copy j)).t)
    (hMixedZero : ∀ js : Fin 3 → Fin k,
      (∀ j : Fin k, js ≠ fun _ ↦ j) →
      PiTensorProduct.map (fun i ↦ f (js i) i) S.t = 0) :
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

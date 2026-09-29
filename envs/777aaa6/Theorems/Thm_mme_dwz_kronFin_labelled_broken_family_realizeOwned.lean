-- Prove2me | Theorems.Thm_mme_dwz_kronFin_labelled_broken_family_realizeOwned
-- name    : mme_dwz_kronFin_labelled_broken_family_realizeOwned
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T12:07:29.376586+00:00
-- url     : https://prove2.me/theorems/855ef311-a3ea-4f2e-b801-8c143ba6982a
-- title:
--   Grouped shuffles and owner projections realize a finite family of broken standard copies
-- statement:
--   Fix a finite family of broken copies of the literal fifteen-component DWZ standard tensor. For every independent family of grouped position shuffles, construct modewise maps from each copy's nonhole subtensor into the common standard tensor. If an owner assignment chooses one copy for every useful block and the inverse-shuffled block is a nonhole of its owner, then these maps can be modified only in mode Z so that copy t maps to exactly the sum of singleton useful-block tensors owned by t. The X- and Y-mode shuffle maps are retained literally. This packages the common-shuffle and owner-selection parts of the Hole Lemma in the exact literal kronFin representation used by the DWZ standard tensor.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 5.7 and Claims 5.8--5.10, especially Claim 5.9 and the owner-based repair in the proof of the Hole Lemma, PDF pp. 49--50 / printed pp. 48--49; https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_dwz_kronFin_labelled_broken_grouped_shuffle_expansion
import Theorems.Thm_mme_dwz_labelled_broken_owner_projection_realizes_exact_sum

open BigOperators Finset
open MME Module PiTensorProduct
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem mme_dwz_kronFin_labelled_broken_family_realizeOwned
    (K : Type u) [Field K] (m : ℕ) {s : ℕ}
    (copies : Fin s →
      MME.DWZSquare.BrokenBlockCopy (DWZStandardBlock m)) :
    let D : DWZStandardLabelledData K m :=
      { X := TensorObj.kronFin 15
          (fun r : Fin 15 ↦ restrictedComponentPower K r m)
        basis := TensorObj.kronFinModePiBasis 15
          (fun r : Fin 15 ↦ restrictedComponentPower K r m) 2
          (fun r ↦ restrictedComponentZBasis K r m)
        label := groupedUsefulBlock m }
    let G : Fin s → D.X.TypeGrading 2 := fun t ↦
      D.X.basisZAllowedGrading D.basis
        (fun W ↦ D.label W ∈ (copies t).nonholes)
    let Shuffle :=
      MME.DWZTable2StandardForm.UsefulBlockShuffleGroup
        (groupedOuter (m := m))
    ∃ shuffleMap : (Fin s → Shuffle) →
        ∀ t i,
          ((G t).blockSubtensor (fun _ ↦ 0)).V i →ₗ[K] D.X.V i,
      ∀ (shuffles : Fin s → Shuffle)
          (owner : DWZStandardBlock m → Fin s),
        (∀ block : DWZStandardBlock m,
          (MulAction.toPerm (shuffles (owner block))).symm block ∈
            (copies (owner block)).nonholes) →
        ∃ f : ∀ t i,
            ((G t).blockSubtensor (fun _ ↦ 0)).V i →ₗ[K] D.X.V i,
          (∀ t, f t 0 = shuffleMap shuffles t 0) ∧
          (∀ t, f t 1 = shuffleMap shuffles t 1) ∧
          ∀ t,
            PiTensorProduct.map (f t)
                ((G t).blockSubtensor (fun _ ↦ 0)).t =
              ∑ block : DWZStandardBlock m,
                if t = owner block then
                  dwzLabelledUsefulBlockTensor K m D block
                else 0 := by
  sorry

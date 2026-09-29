-- Prove2me | solution 1 for mme_dwz_kronFin_hole_cover_restrict_standard
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T12:36:04.25566+00:00
-- url     : https://prove2.me/submissions/3e44e963-d733-4d59-8f84-3054f32bc41d

import Theorems.Thm_mme_dwz_kronFin_hole_cover_tensor_repair
import Theorems.Thm_mme_dwz_labelled_sum_useful_block_tensors_eq

open BigOperators Finset
open MME Module PiTensorProduct
open MME.DWZSquare MME.DWZTable2StandardForm
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option maxHeartbeats 800000

theorem solution
    (K : Type u) [Field K] (m N ell : ℕ) {s : ℕ}
    (hN : 0 < N) (hell : 0 < ell)
    (copies : Fin s → BrokenBlockCopy (DWZStandardBlock m))
    (hcard : Fintype.card (DWZStandardBlock m) ≤ 2 ^ (N * ell))
    (hsum : ((N * ell + 1 : ℕ) : ℝ) ≤
      ∑ t : Fin s, nonholeFraction (copies t)) :
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
    TensorObj.Restrict D.X
      (TensorObj.bigAdd
        (fun t ↦ (G t).blockSubtensor (fun _ ↦ 0))) := by
  classical
  dsimp only
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
  have hrepair := mme_dwz_kronFin_hole_cover_tensor_repair
    K m N ell hN hell copies hcard hsum
  change TensorObj.Restrict
    ({ V := D.X.V
       t := ∑ block : DWZStandardBlock m,
         dwzLabelledUsefulBlockTensor K m D block } : TensorObj K 3)
    (TensorObj.bigAdd
      (fun t ↦ (G t).blockSubtensor (fun _ ↦ 0))) at hrepair
  rw [mme_dwz_labelled_sum_useful_block_tensors_eq] at hrepair
  exact hrepair

-- Prove2me | solution 1 for mme_dwz_flat_seven_eighths_restrict_standard
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T13:41:06.668468+00:00
-- url     : https://prove2.me/submissions/aaa87636-7c28-41e4-b47f-7651b705db8b

import Theorems.Thm_mme_dwz_grouped_seven_eighths_restrict_standard

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
    (K : Type u) [Field K] (m N ell k : ℕ)
    (hN : 0 < N) (hell : 0 < ell)
    (copies : Fin (k * (8 * (N * ell + 1))) →
      BrokenBlockCopy (DWZStandardBlock m))
    (hcard : Fintype.card (DWZStandardBlock m) ≤ 2 ^ (N * ell))
    (hseven : ∀ r,
      7 * Fintype.card (DWZStandardBlock m) ≤
        8 * (copies r).nonholes.card) :
    let D : DWZStandardLabelledData K m :=
      { X := TensorObj.kronFin 15
          (fun r : Fin 15 ↦ restrictedComponentPower K r m)
        basis := TensorObj.kronFinModePiBasis 15
          (fun r : Fin 15 ↦ restrictedComponentPower K r m) 2
          (fun r ↦ restrictedComponentZBasis K r m)
        label := groupedUsefulBlock m }
    let G : Fin (k * (8 * (N * ell + 1))) → D.X.TypeGrading 2 :=
      fun r ↦ D.X.basisZAllowedGrading D.basis
        (fun W ↦ D.label W ∈ (copies r).nonholes)
    TensorObj.Restrict
      (TensorObj.bigAdd (fun _ : Fin k ↦ D.X))
      (TensorObj.bigAdd (fun r ↦
        (G r).blockSubtensor (fun _ ↦ 0))) := by
  classical
  let groupedCopies : Fin k → Fin (8 * (N * ell + 1)) →
      BrokenBlockCopy (DWZStandardBlock m) :=
    fun a b ↦ copies (finProdFinEquiv (a, b))
  have h := mme_dwz_grouped_seven_eighths_restrict_standard
    K m N ell k hN hell groupedCopies hcard
      (fun a b ↦ hseven (finProdFinEquiv (a, b)))
  simpa only [groupedCopies, Prod.eta, Equiv.apply_symm_apply] using h

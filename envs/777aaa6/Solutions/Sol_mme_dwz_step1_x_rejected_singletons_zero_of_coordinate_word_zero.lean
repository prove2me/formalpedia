-- Prove2me | solution 1 for mme_dwz_step1_x_rejected_singletons_zero_of_coordinate_word_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-28T11:12:17.867615+00:00
-- url     : https://prove2.me/submissions/30b728e0-e701-40d6-8018-14f2af9ca932

import Definitions.Def_mme_dwz_step1_rejected_singleton_properties
import Theorems.Thm_mme_basisZAllowed_map_eq_zero_of_selected_singletons
import Theorems.Thm_mme_piTensorProduct_map_eq_zero_of_selected_basis_singletons_at_mode
import Theorems.Thm_mme_dwz_source_address_useful_z_supported_implies_step1_words

open MME Module PiTensorProduct
open MME.DWZStep1Support
open MME.DWZSourceAligned

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
set_option maxRecDepth 12000

theorem solution
    {K : Type u} [Field K]
    (m : ℕ) {N : ℕ} (outer : Fin N → Fin 15)
    (copy : DWZSquare.BrokenBlockCopy
      (DWZTable2StandardForm.UsefulBlock m outer))
    (hCoordinateZero : BrokenOwnerCoordinateZeroProperty
      K m outer copy) :
    Step1XRejectedSingletonZeroProperty K m outer copy := by
  classical
  unfold BrokenOwnerCoordinateZeroProperty at hCoordinateZero
  unfold Step1XRejectedSingletonZeroProperty
  let T := coarseAddressObj K outer
  let G := brokenAddressGrading K m outer copy
  let base : ∀ i : Fin 3, T.V i →ₗ[K] G.classOf i 0 :=
    fun i ↦ G.blockProj i 0
  intro x hx
  dsimp only
  let sx : T.V 0 →ₗ[K] T.V 0 :=
    DWZComponentRestriction.basisLabelProjection
      (coarseAddressModeBasis K outer 0) id {x}
  let pre : ∀ i : Fin 3, T.V i →ₗ[K] T.V i :=
    Function.update (fun _ ↦ LinearMap.id) 0 sx
  have hZ := mme_basisZAllowed_map_eq_zero_of_selected_singletons
    (S := T) (T := T)
    (coarseAddressZBasis K outer)
    (addressWordSurvives m outer copy) pre
    (by
      intro z hz
      dsimp only
      obtain ⟨hUseful, hNonhole⟩ := hz
      let sz : T.V 2 →ₗ[K] T.V 2 :=
        DWZComponentRestriction.basisLabelProjection
          (coarseAddressZBasis K outer) id {z}
      let zMaps : ∀ i : Fin 3, T.V i →ₗ[K] G.classOf i 0 :=
        Function.update
          (fun i ↦ (G.blockProj i 0).comp (pre i)) 2
          (((G.blockProj 2 0).comp sz).comp (pre 2))
      apply mme_piTensorProduct_map_eq_zero_of_selected_basis_singletons_at_mode
        (K := K) (d := 3) (S := T) (U := G.blockSubtensor (fun _ ↦ 0))
        1 (coarseAddressModeBasis K outer 1) (fun _ ↦ True)
        LinearMap.id (G.blockProj 1 0) zMaps
      · apply DFunLike.ext _ _
        intro v
        rfl
      · intro y hy
        exact (hy trivial).elim
      · intro y _hy
        dsimp only
        let sy : T.V 1 →ₗ[K] T.V 1 :=
          DWZComponentRestriction.basisLabelProjection
            (coarseAddressModeBasis K outer 1) id {y}
        by_cases hzero : ∃ r : Fin N,
            (cwSquareFineSplitGrading K 6).blockTensor
              (fun i ↦ ![
                MME.DWZStep1Support.fineSplitGrade
                  (addressModeLeftGrade x r)
                  (addressModeRightGrade x r),
                MME.DWZStep1Support.fineSplitGrade
                  (addressModeLeftGrade y r)
                  (addressModeRightGrade y r),
                MME.DWZStep1Support.fineSplitGrade
                  (z r).leftGrade (z r).rightGrade] i) = 0
        · have h := hCoordinateZero x y z hzero
          dsimp only at h
          have hmaps :
              (fun i ↦ (G.blockProj i 0).comp
                ((Function.update
                  (Function.update
                    (Function.update (fun _ ↦ LinearMap.id) 0 sx)
                    1 sy) 2 sz) i)) =
              Function.update zMaps 1 ((G.blockProj 1 0).comp sy) := by
            funext i
            fin_cases i <;> rfl
          rw [hmaps] at h
          exact h
        · have hSupported : ∀ r : Fin N,
              (cwSquareFineSplitGrading K 6).blockTensor
                (fun i ↦ ![
                  MME.DWZStep1Support.fineSplitGrade
                    (addressModeLeftGrade x r)
                    (addressModeRightGrade x r),
                  MME.DWZStep1Support.fineSplitGrade
                    (addressModeLeftGrade y r)
                    (addressModeRightGrade y r),
                  MME.DWZStep1Support.fineSplitGrade
                    (z r).leftGrade (z r).rightGrade] i) ≠ 0 := by
            intro r hr
            exact hzero ⟨r, hr⟩
          have hPass :=
            (mme_dwz_source_address_useful_z_supported_implies_step1_words
              m outer x y z hUseful hSupported).1
          exact (hx hPass).elim)
  dsimp only at hZ
  change PiTensorProduct.map
      (fun i ↦ (G.blockProj i 0).comp (pre i)) T.t = 0 at hZ
  let xMaps := Function.update base 0 ((base 0).comp sx)
  have hmaps : (fun i ↦ (G.blockProj i 0).comp (pre i)) = xMaps := by
    funext i
    fin_cases i <;> rfl
  rw [hmaps] at hZ
  simpa only [T, G, base, sx, xMaps] using hZ

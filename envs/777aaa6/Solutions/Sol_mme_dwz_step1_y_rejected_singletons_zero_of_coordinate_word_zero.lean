-- Prove2me | solution 1 for mme_dwz_step1_y_rejected_singletons_zero_of_coordinate_word_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-28T11:13:41.162254+00:00
-- url     : https://prove2.me/submissions/73214585-0c5f-4c96-bf53-ab6f2ad9f00e

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
    Step1YRejectedSingletonZeroProperty K m outer copy := by
  classical
  unfold BrokenOwnerCoordinateZeroProperty at hCoordinateZero
  unfold Step1YRejectedSingletonZeroProperty
  let T := coarseAddressObj K outer
  let G := brokenAddressGrading K m outer copy
  let base : ∀ i : Fin 3, T.V i →ₗ[K] G.classOf i 0 :=
    fun i ↦ G.blockProj i 0
  intro y hy
  dsimp only
  let sy : T.V 1 →ₗ[K] T.V 1 :=
    DWZComponentRestriction.basisLabelProjection
      (coarseAddressModeBasis K outer 1) id {y}
  let pre : ∀ i : Fin 3, T.V i →ₗ[K] T.V i :=
    Function.update
      (Function.update (fun _ ↦ LinearMap.id) 0
        (addressXStep1Projector K m outer)) 1 sy
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
        0 (coarseAddressModeBasis K outer 0)
        (addressXWordPassesStep1 m outer)
        LinearMap.id ((G.blockProj 0 0).comp
          (addressXStep1Projector K m outer)) zMaps
      · apply DFunLike.ext _ _
        intro v
        rfl
      · intro x hx
        change (G.blockProj 0 0)
          (addressXStep1Projector K m outer
            (coarseAddressModeBasis K outer 0 x)) = 0
        rw [addressXStep1Projector_apply_basis_of_not_passes
          m outer x hx]
        exact map_zero (G.blockProj 0 0)
      · intro x hx
        dsimp only
        have hAbsorb :=
          addressXStep1Projector_comp_singleton_of_passes
            (K := K) m outer x hx
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
          let sx : T.V 0 →ₗ[K] T.V 0 :=
            DWZComponentRestriction.basisLabelProjection
              (coarseAddressModeBasis K outer 0) id {x}
          let selected : ∀ i : Fin 3, T.V i →ₗ[K] T.V i :=
            Function.update
              (Function.update
                (Function.update (fun _ ↦ LinearMap.id) 0 sx) 1 sy) 2 sz
          let targetMaps := Function.update zMaps 0
            ((((G.blockProj 0 0).comp
              (addressXStep1Projector K m outer)).comp sx).comp
              LinearMap.id)
          change PiTensorProduct.map
              (fun i ↦ (G.blockProj i 0).comp (selected i)) T.t = 0 at h
          have hmaps :
              (fun i ↦ (G.blockProj i 0).comp (selected i)) =
                targetMaps := by
            funext i
            fin_cases i
            · apply DFunLike.ext _ _
              intro v
              change (G.blockProj 0 0) (sx v) =
                (G.blockProj 0 0)
                  (addressXStep1Projector K m outer (sx v))
              exact congrArg (G.blockProj 0 0)
                (LinearMap.congr_fun hAbsorb v).symm
            · rfl
            · rfl
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
              m outer x y z hUseful hSupported).2
          exact (hy hPass).elim)
  dsimp only at hZ
  change PiTensorProduct.map
      (fun i ↦ (G.blockProj i 0).comp (pre i)) T.t = 0 at hZ
  let xMaps := Function.update base 0
    ((base 0).comp (addressXStep1Projector K m outer))
  let xyMaps := Function.update xMaps 1 ((xMaps 1).comp sy)
  have hxy : (fun i ↦ (G.blockProj i 0).comp (pre i)) = xyMaps := by
    funext i
    fin_cases i <;> rfl
  rw [hxy] at hZ
  simpa only [T, G, base, sy, xMaps, xyMaps] using hZ

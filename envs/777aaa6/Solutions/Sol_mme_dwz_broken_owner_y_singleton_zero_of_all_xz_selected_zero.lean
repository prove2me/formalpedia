-- Prove2me | solution 1 for mme_dwz_broken_owner_y_singleton_zero_of_all_xz_selected_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T23:35:06.748286+00:00
-- url     : https://prove2.me/submissions/e0322846-337b-4017-9d2c-23f6932e935a

import Theorems.Thm_mme_basisZAllowed_map_eq_zero_of_selected_singletons
import Theorems.Thm_mme_piTensorProduct_map_eq_zero_of_selected_basis_singletons_at_mode
import Definitions.Def_mme_dwz_step1_projector_basis_api

open MME Module PiTensorProduct

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

open MME.DWZSourceAligned

/-- If every accepted X word and surviving Z word kills a fixed Y singleton,
then the complete X Step-1 filter and Z mask kill that Y singleton. -/
theorem solution
    {K : Type u} [Field K]
    (m : ℕ) {N : ℕ} (outer : Fin N → Fin 15)
    (copy : DWZSquare.BrokenBlockCopy
      (DWZTable2StandardForm.UsefulBlock m outer))
    (y : AddressModeWord outer 1)
    (hTripleZero : ∀ (x : AddressModeWord outer 0),
      addressXWordPassesStep1 m outer x →
      ∀ (z : AddressZWord outer),
      addressWordSurvives m outer copy z →
      let G := brokenAddressGrading K m outer copy
      let sx := DWZComponentRestriction.basisLabelProjection
        (coarseAddressModeBasis K outer 0) id {x}
      let sy := DWZComponentRestriction.basisLabelProjection
        (coarseAddressModeBasis K outer 1) id {y}
      let sz := DWZComponentRestriction.basisLabelProjection
        (coarseAddressZBasis K outer) id {z}
      let selected : ∀ i : Fin 3,
          (coarseAddressObj K outer).V i →ₗ[K]
            (coarseAddressObj K outer).V i :=
        Function.update
          (Function.update
            (Function.update (fun _ ↦ LinearMap.id) 0 sx) 1 sy) 2 sz
      PiTensorProduct.map
        (fun i ↦ (G.blockProj i 0).comp (selected i))
        (coarseAddressObj K outer).t = 0) :
    let G := brokenAddressGrading K m outer copy
    let base : ∀ i : Fin 3,
        (coarseAddressObj K outer).V i →ₗ[K] G.classOf i 0 :=
      fun i ↦ G.blockProj i 0
    let xMaps := Function.update base 0
      ((base 0).comp (addressXStep1Projector K m outer))
    let sy := DWZComponentRestriction.basisLabelProjection
      (coarseAddressModeBasis K outer 1) id {y}
    PiTensorProduct.map
      (Function.update xMaps 1 ((xMaps 1).comp sy))
      (coarseAddressObj K outer).t = 0 := by
  classical
  dsimp only
  let T := coarseAddressObj K outer
  let G := brokenAddressGrading K m outer copy
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
      · rfl
      · intro x hx
        change (G.blockProj 0 0)
          (addressXStep1Projector K m outer
            (coarseAddressModeBasis K outer 0 x)) = 0
        rw [addressXStep1Projector_apply_basis_of_not_passes
          m outer x hx]
        exact LinearMap.map_zero _
      · intro x hx
        dsimp only
        let sx : T.V 0 →ₗ[K] T.V 0 :=
          DWZComponentRestriction.basisLabelProjection
            (coarseAddressModeBasis K outer 0) id {x}
        let selected : ∀ i : Fin 3, T.V i →ₗ[K] T.V i :=
          Function.update
            (Function.update
              (Function.update (fun _ ↦ LinearMap.id) 0 sx) 1 sy) 2 sz
        have h := hTripleZero x hx z hz
        change PiTensorProduct.map
          (fun i ↦ (G.blockProj i 0).comp (selected i)) T.t = 0 at h
        have hAbsorb :=
          addressXStep1Projector_comp_singleton_of_passes
            (K := K) m outer x hx
        have hmaps : Function.update zMaps 0
              ((((G.blockProj 0 0).comp
                (addressXStep1Projector K m outer)).comp
                (DWZComponentRestriction.basisLabelProjection
                  (coarseAddressModeBasis K outer 0) id {x})).comp
                LinearMap.id) =
            (fun i ↦ (G.blockProj i 0).comp (selected i)) := by
          funext i
          fin_cases i
          · simp only [LinearMap.comp_id,
              LinearMap.comp_assoc, hAbsorb]
            rfl
          · rfl
          · rfl
        exact (congrArg
          (fun maps ↦ PiTensorProduct.map maps T.t) hmaps).trans h)
  dsimp only at hZ
  change PiTensorProduct.map
    (fun i ↦ (G.blockProj i 0).comp (pre i)) T.t = 0 at hZ
  let base : ∀ i : Fin 3, T.V i →ₗ[K] G.classOf i 0 :=
    fun i ↦ G.blockProj i 0
  let xMaps := Function.update base 0
    ((base 0).comp (addressXStep1Projector K m outer))
  let xyMaps := Function.update xMaps 1 ((xMaps 1).comp sy)
  have hmaps : (fun i ↦ (G.blockProj i 0).comp (pre i)) = xyMaps := by
    funext i
    fin_cases i <;> rfl
  have htransport := congrArg
    (fun maps ↦ PiTensorProduct.map maps T.t) hmaps
  have hxyMaps : PiTensorProduct.map xyMaps T.t = 0 :=
    htransport.symm.trans hZ
  simpa only [T, G, base, sy, xMaps, xyMaps] using hxyMaps

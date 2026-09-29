-- Prove2me | solution 1 for mme_dwz_step1_filtered_broken_address_maps_preserve_tensor_of_rejected_singletons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T23:10:53.374746+00:00
-- url     : https://prove2.me/submissions/36e83f16-c01e-4b1b-b203-cbbc901e7ef2

import Definitions.Def_mme_dwz_step1_broken_owner_maps
import Theorems.Thm_mme_piTensorProduct_map_basis_filter_eq_of_rejected_singletons_zero

open MME Module PiTensorProduct
open MME.DWZSourceAligned

universe u


set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 10000

theorem solution
    {K : Type u} [Field K]
    (m : ℕ) {N : ℕ} (outer : Fin N → Fin 15)
    (copy : DWZSquare.BrokenBlockCopy
      (DWZTable2StandardForm.UsefulBlock m outer))
    (hXZero : ∀ (x : AddressModeWord outer 0),
      ¬ addressXWordPassesStep1 m outer x →
      let G := brokenAddressGrading K m outer copy
      let base : ∀ i : Fin 3,
          (coarseAddressObj K outer).V i →ₗ[K] G.classOf i 0 :=
        fun i ↦ G.blockProj i 0
      let singleton :=
        DWZComponentRestriction.basisLabelProjection
          (coarseAddressModeBasis K outer 0) id {x}
      PiTensorProduct.map
        (Function.update base 0 ((base 0).comp singleton))
        (coarseAddressObj K outer).t = 0)
    (hYZero : ∀ (y : AddressModeWord outer 1),
      ¬ addressYWordPassesStep1 m outer y →
      let G := brokenAddressGrading K m outer copy
      let base : ∀ i : Fin 3,
          (coarseAddressObj K outer).V i →ₗ[K] G.classOf i 0 :=
        fun i ↦ G.blockProj i 0
      let xMaps := Function.update base 0
        ((base 0).comp (addressXStep1Projector K m outer))
      let singleton :=
        DWZComponentRestriction.basisLabelProjection
          (coarseAddressModeBasis K outer 1) id {y}
      PiTensorProduct.map
        (Function.update xMaps 1 ((xMaps 1).comp singleton))
        (coarseAddressObj K outer).t = 0) :
    PiTensorProduct.map
        (step1FilteredBrokenAddressMaps K m outer copy)
        (coarseAddressObj K outer).t =
      (brokenAddressObj K m outer copy).t := by
  classical
  let T := coarseAddressObj K outer
  let G := brokenAddressGrading K m outer copy
  let base : ∀ i : Fin 3, T.V i →ₗ[K] G.classOf i 0 :=
    fun i ↦ G.blockProj i 0
  let xMaps : ∀ i : Fin 3, T.V i →ₗ[K] G.classOf i 0 :=
    Function.update base 0
      ((base 0).comp (addressXStep1Projector K m outer))
  let xyMaps : ∀ i : Fin 3, T.V i →ₗ[K] G.classOf i 0 :=
    Function.update xMaps 1
      ((xMaps 1).comp (addressYStep1Projector K m outer))
  have hX : PiTensorProduct.map xMaps T.t =
      PiTensorProduct.map base T.t := by
    have h :=
      mme_piTensorProduct_map_basis_filter_eq_of_rejected_singletons_zero
        (K := K) (d := 3) (S := T) (U := G.blockSubtensor (fun _ ↦ 0))
        0 (coarseAddressModeBasis K outer 0)
        (addressXWordPassesStep1 m outer) base
        (by
          intro x hx
          simpa only [T, G, base] using hXZero x hx)
    simpa only [T, G, base, xMaps, addressXStep1Projector] using h
  have hY : PiTensorProduct.map xyMaps T.t =
      PiTensorProduct.map xMaps T.t := by
    have h :=
      mme_piTensorProduct_map_basis_filter_eq_of_rejected_singletons_zero
        (K := K) (d := 3) (S := T) (U := G.blockSubtensor (fun _ ↦ 0))
        1 (coarseAddressModeBasis K outer 1)
        (addressYWordPassesStep1 m outer) xMaps
        (by
          intro y hy
          simpa only [T, G, base, xMaps] using hYZero y hy)
    simpa only [T, G, xMaps, xyMaps, addressYStep1Projector] using h
  have hmaps : xyMaps = step1FilteredBrokenAddressMaps K m outer copy := by
    funext i
    fin_cases i <;>
      rfl
  rw [← hmaps]
  change PiTensorProduct.map xyMaps T.t =
    (brokenAddressObj K m outer copy).t
  rw [hY, hX]
  rfl

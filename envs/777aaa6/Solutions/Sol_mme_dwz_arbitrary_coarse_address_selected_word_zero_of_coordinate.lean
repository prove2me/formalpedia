-- Prove2me | solution 1 for mme_dwz_arbitrary_coarse_address_selected_word_zero_of_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-28T11:37:30.956412+00:00
-- url     : https://prove2.me/submissions/596ed8ee-f274-46f8-bb8e-83c1d26b5986

import Definitions.Def_mme_dwz_step1_mixed_selected_full_map_data
import Theorems.Thm_mme_dwz_arbitrary_coarse_component_singleton_zero_of_fine_block
import Theorems.Thm_mme_kronFin_selected_basis_postmap_eq_zero_of_coordinate

open MME Module PiTensorProduct
open MME.DWZStep1Support
open MME.DWZSourceAligned

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
set_option maxRecDepth 12000

theorem solution
    {K : Type u} [Field K] {N : ℕ}
    (address : Fin 3 → Fin N → Fin 5)
    (selected : ∀ i r,
      DWZComponentRestriction.LiftedCoarsePair.{u} 6 (address i r))
    {W : Fin 3 → Type u}
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (post : ∀ i,
      (gradedAddressBlock (cwSquareCanonicalGrading K 6) address).V i →ₗ[K]
        W i)
    (r : Fin N)
    (hzero : (cwSquareFineSplitGrading K 6).blockTensor
      (fun i ↦ fineSplitGrade
        (selected i r).leftGrade (selected i r).rightGrade) = 0) :
    PiTensorProduct.map
        (fun i ↦ (post i).comp
          (DWZComponentRestriction.basisLabelProjection
            (arbitraryCoarseAddressModeBasis K address i) id {selected i}))
        (gradedAddressBlock (cwSquareCanonicalGrading K 6) address).t = 0 := by
  let X : Fin N → TensorObj K 3 := fun t ↦
    (cwSquareCanonicalGrading K 6).blockSubtensor
      (fun i ↦ address i t)
  let Index : Fin N → Fin 3 → Type u := fun t i ↦
    DWZComponentRestriction.LiftedCoarsePair.{u} 6 (address i t)
  let b : ∀ t i, Basis (Index t i) K ((X t).V i) :=
    fun t i ↦ arbitraryCoarseComponentModeBasis K
      (fun j ↦ address j t) i
  have hlocal : PiTensorProduct.map
      (fun i ↦ DWZComponentRestriction.basisLabelProjection
        (b r i) id {selected i r}) (X r).t = 0 := by
    simpa only [X, Index, b, LinearMap.id_comp] using
      (mme_dwz_arbitrary_coarse_component_singleton_zero_of_fine_block
        (K := K) (fun i ↦ address i r) (fun i ↦ selected i r)
        (fun _ ↦ LinearMap.id) hzero)
  have h := mme_kronFin_selected_basis_postmap_eq_zero_of_coordinate
    X b selected post r hlocal
  simpa only [X, Index, b, arbitraryCoarseAddressModeBasis,
    gradedAddressBlock] using h

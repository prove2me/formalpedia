-- Prove2me | solution 1 for mme_dwz_coarseAddress_selected_mode_words_postmap_eq_zero_of_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-28T10:26:25.695736+00:00
-- url     : https://prove2.me/submissions/fcf665fa-58f5-43f9-9626-ebaebf1825ee

import Definitions.Def_mme_dwz_step1_projector_basis_api
import Theorems.Thm_mme_kronFin_selected_basis_postmap_eq_zero_of_coordinate
import Theorems.Thm_mme_dwz_canonicalComponent_selected_singleton_postmap_eq_zero_of_fine_block

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
    (outer : Fin N → Fin 15)
    (word : ∀ i : Fin 3, AddressModeWord outer i)
    {W : Fin 3 → Type u}
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (post : ∀ i, (coarseAddressObj K outer).V i →ₗ[K] W i)
    (r : Fin N)
    (hzero : (cwSquareFineSplitGrading K 6).blockTensor
      (fun i ↦ fineSplitGrade
        (word i r).leftGrade (word i r).rightGrade) = 0) :
    PiTensorProduct.map
        (fun i ↦ (post i).comp
          (DWZComponentRestriction.basisLabelProjection
            (coarseAddressModeBasis K outer i) id {word i}))
        (coarseAddressObj K outer).t = 0 := by
  let X : Fin N → TensorObj K 3 :=
    fun t ↦ DWZComponentRestriction.canonicalComponentBlock K (outer t)
  let Index : Fin N → Fin 3 → Type u := fun t i ↦
    DWZComponentRestriction.LiftedCoarsePair.{u} 6
      (cwSquareBlockType
        (DWZSquare.shapeX (outer t))
        (DWZSquare.shapeY (outer t))
        (DWZSquare.shapeZ (outer t)) i)
  let b : ∀ t i, Basis (Index t i) K ((X t).V i) :=
    fun t i ↦ canonicalComponentModeBasis K (outer t) i
  have hlocal : PiTensorProduct.map
      (fun i ↦ DWZComponentRestriction.basisLabelProjection
        (b r i) id {word i r}) (X r).t = 0 := by
    simpa only [X, Index, b, LinearMap.id_comp] using
      (mme_dwz_canonicalComponent_selected_singleton_postmap_eq_zero_of_fine_block
        (K := K) (outer r) (fun i ↦ word i r)
        (fun _ ↦ LinearMap.id) hzero)
  have h := mme_kronFin_selected_basis_postmap_eq_zero_of_coordinate
    X b word post r hlocal
  simpa only [X, Index, b, coarseAddressObj, gradedAddressBlock,
    coarseAddress] using h

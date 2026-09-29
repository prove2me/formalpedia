-- Prove2me | Definitions.Def_mme_dwz_step1_rejected_singleton_properties
-- name    : mme_dwz_step1_rejected_singleton_properties
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-28T11:05:38.453719+00:00
-- url     : https://prove2.me/theorems/109cd5d9-1958-4277-81ed-1ea00abcfade
-- title:
--   Rejected singleton properties for Step-1 broken-owner filtering
-- statement:
--   This interface names the three tensor-vanishing properties used in Additional Zeroing-Out Step 1 for one broken owner: vanishing of a selected X/Y/Z word whenever one fine coordinate is unsupported, vanishing of each X singleton rejected by the X histogram filter, and vanishing of each Y singleton rejected after the X filter has been inserted. The definitions expose no additional hypothesis; they package the exact propositions consumed by the two filter-preservation branches.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6, Additional Zeroing-Out Step 1; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_step1_projector_basis_api
import Definitions.Def_mme_dwz_cw_square_fine_split_grading

open MME Module PiTensorProduct
open MME.DWZStep1Support

universe u

set_option autoImplicit false

namespace MME.DWZSourceAligned

def BrokenOwnerCoordinateZeroProperty
    (K : Type u) [Field K]
    (m : ℕ) {N : ℕ} (outer : Fin N → Fin 15)
    (copy : DWZSquare.BrokenBlockCopy
      (DWZTable2StandardForm.UsefulBlock m outer)) : Prop :=
  ∀ (x : AddressModeWord outer 0)
    (y : AddressModeWord outer 1)
    (z : AddressZWord outer),
    (∃ r : Fin N,
      (cwSquareFineSplitGrading K 6).blockTensor
        (fun i ↦ ![
          fineSplitGrade
            (addressModeLeftGrade x r) (addressModeRightGrade x r),
          fineSplitGrade
            (addressModeLeftGrade y r) (addressModeRightGrade y r),
          fineSplitGrade (z r).leftGrade (z r).rightGrade] i) = 0) →
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
      (coarseAddressObj K outer).t = 0

def Step1XRejectedSingletonZeroProperty
    (K : Type u) [Field K]
    (m : ℕ) {N : ℕ} (outer : Fin N → Fin 15)
    (copy : DWZSquare.BrokenBlockCopy
      (DWZTable2StandardForm.UsefulBlock m outer)) : Prop :=
  ∀ (x : AddressModeWord outer 0),
    ¬ addressXWordPassesStep1 m outer x →
    let G := brokenAddressGrading K m outer copy
    let base : ∀ i : Fin 3,
        (coarseAddressObj K outer).V i →ₗ[K] G.classOf i 0 :=
      fun i ↦ G.blockProj i 0
    let singleton := DWZComponentRestriction.basisLabelProjection
      (coarseAddressModeBasis K outer 0) id {x}
    PiTensorProduct.map
      (Function.update base 0 ((base 0).comp singleton))
      (coarseAddressObj K outer).t = 0

def Step1YRejectedSingletonZeroProperty
    (K : Type u) [Field K]
    (m : ℕ) {N : ℕ} (outer : Fin N → Fin 15)
    (copy : DWZSquare.BrokenBlockCopy
      (DWZTable2StandardForm.UsefulBlock m outer)) : Prop :=
  ∀ (y : AddressModeWord outer 1),
    ¬ addressYWordPassesStep1 m outer y →
    let G := brokenAddressGrading K m outer copy
    let base : ∀ i : Fin 3,
        (coarseAddressObj K outer).V i →ₗ[K] G.classOf i 0 :=
      fun i ↦ G.blockProj i 0
    let xMaps := Function.update base 0
      ((base 0).comp (addressXStep1Projector K m outer))
    let singleton := DWZComponentRestriction.basisLabelProjection
      (coarseAddressModeBasis K outer 1) id {y}
    PiTensorProduct.map
      (Function.update xMaps 1 ((xMaps 1).comp singleton))
      (coarseAddressObj K outer).t = 0

end MME.DWZSourceAligned



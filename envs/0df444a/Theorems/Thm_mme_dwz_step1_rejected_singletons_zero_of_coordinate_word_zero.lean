-- Prove2me | Theorems.Thm_mme_dwz_step1_rejected_singletons_zero_of_coordinate_word_zero
-- name    : mme_dwz_step1_rejected_singletons_zero_of_coordinate_word_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-28T10:23:44.109643+00:00
-- url     : https://prove2.me/theorems/1c7c1349-3f28-4f85-bd7a-1cf9876c5e60
-- title:
--   Coordinate vanishing supplies both rejected Step-1 singleton zeros
-- statement:
--   If every selected X/Y/Z address-word triple with a zero fine coordinate is annihilated after broken-block projection, then every X word rejected by the Step-1 X filter and every Y word rejected after the Step-1 X filter are annihilated.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6, Additional Zeroing-Out Step 1; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_step1_projector_basis_api
import Definitions.Def_mme_dwz_cw_square_fine_split_grading
import Theorems.Thm_mme_basisZAllowed_map_eq_zero_of_selected_singletons
import Theorems.Thm_mme_piTensorProduct_map_eq_zero_of_selected_basis_singletons_at_mode
import Theorems.Thm_mme_dwz_source_address_useful_z_supported_implies_step1_words

open MME Module PiTensorProduct
open MME.DWZStep1Support
open MME.DWZSourceAligned

universe u

set_option autoImplicit false

theorem mme_dwz_step1_rejected_singletons_zero_of_coordinate_word_zero
    {K : Type u} [Field K]
    (m : ℕ) {N : ℕ} (outer : Fin N → Fin 15)
    (copy : DWZSquare.BrokenBlockCopy
      (DWZTable2StandardForm.UsefulBlock m outer))
    (hCoordinateZero : ∀
      (x : AddressModeWord outer 0)
      (y : AddressModeWord outer 1)
      (z : AddressZWord outer),
      (∃ r : Fin N,
        (cwSquareFineSplitGrading K 6).blockTensor
          (fun i ↦ ![
            MME.DWZStep1Support.fineSplitGrade
              (addressModeLeftGrade x r)
              (addressModeRightGrade x r),
            MME.DWZStep1Support.fineSplitGrade
              (addressModeLeftGrade y r)
              (addressModeRightGrade y r),
            MME.DWZStep1Support.fineSplitGrade
              (z r).leftGrade (z r).rightGrade] i) = 0) →
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
    (∀ (x : AddressModeWord outer 0),
      ¬ addressXWordPassesStep1 m outer x →
      let G := brokenAddressGrading K m outer copy
      let base : ∀ i : Fin 3,
          (coarseAddressObj K outer).V i →ₗ[K] G.classOf i 0 :=
        fun i ↦ G.blockProj i 0
      let singleton := DWZComponentRestriction.basisLabelProjection
        (coarseAddressModeBasis K outer 0) id {x}
      PiTensorProduct.map
        (Function.update base 0 ((base 0).comp singleton))
        (coarseAddressObj K outer).t = 0) ∧
    (∀ (y : AddressModeWord outer 1),
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
        (coarseAddressObj K outer).t = 0) := by
  sorry

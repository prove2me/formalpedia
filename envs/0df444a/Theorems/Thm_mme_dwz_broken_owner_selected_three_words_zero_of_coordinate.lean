-- Prove2me | Theorems.Thm_mme_dwz_broken_owner_selected_three_words_zero_of_coordinate
-- name    : mme_dwz_broken_owner_selected_three_words_zero_of_coordinate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-28T10:44:36.06877+00:00
-- url     : https://prove2.me/theorems/2f2db7ca-ff72-420d-bcf1-0df3cbda7313
-- title:
--   One zero fine coordinate kills a selected broken-owner word
-- statement:
--   For one broken owner, if the square-CW fine block of selected X, Y, and Z address words vanishes in one coordinate, then the corresponding three singleton-selected and broken-block-projected tensor map is zero.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6, Additional Zeroing-Out Step 1; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_step1_projector_basis_api
import Definitions.Def_mme_dwz_cw_square_fine_split_grading
import Theorems.Thm_mme_dwz_coarseAddress_selected_mode_words_postmap_eq_zero_of_coordinate

open MME Module PiTensorProduct
open MME.DWZStep1Support
open MME.DWZSourceAligned

universe u

set_option autoImplicit false

theorem mme_dwz_broken_owner_selected_three_words_zero_of_coordinate
    {K : Type u} [Field K]
    (m : ℕ) {N : ℕ} (outer : Fin N → Fin 15)
    (copy : DWZSquare.BrokenBlockCopy
      (DWZTable2StandardForm.UsefulBlock m outer))
    (x : AddressModeWord outer 0)
    (y : AddressModeWord outer 1)
    (z : AddressZWord outer)
    (hzero : ∃ r : Fin N,
      (cwSquareFineSplitGrading K 6).blockTensor
        (fun i ↦ ![
          MME.DWZStep1Support.fineSplitGrade
            (addressModeLeftGrade x r)
            (addressModeRightGrade x r),
          MME.DWZStep1Support.fineSplitGrade
            (addressModeLeftGrade y r)
            (addressModeRightGrade y r),
          MME.DWZStep1Support.fineSplitGrade
            (z r).leftGrade (z r).rightGrade] i) = 0) :
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
      (coarseAddressObj K outer).t = 0 := by
  sorry

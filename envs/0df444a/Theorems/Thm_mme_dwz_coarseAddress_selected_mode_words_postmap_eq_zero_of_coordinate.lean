-- Prove2me | Theorems.Thm_mme_dwz_coarseAddress_selected_mode_words_postmap_eq_zero_of_coordinate
-- name    : mme_dwz_coarseAddress_selected_mode_words_postmap_eq_zero_of_coordinate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-28T10:24:34.95706+00:00
-- url     : https://prove2.me/theorems/416d1419-47b3-4ba9-aa6b-4e314b55dacb
-- title:
--   A zero fine coordinate kills a selected coarse-address word
-- statement:
--   For a canonical coarse address, a zero fine square-CW block in one coordinate annihilates the complete selected three-mode address word even after arbitrary linear postmaps.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6, Additional Zeroing-Out Step 1; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_step1_projector_basis_api
import Definitions.Def_mme_dwz_cw_square_fine_split_grading

open MME Module PiTensorProduct
open MME.DWZStep1Support
open MME.DWZSourceAligned

universe u

set_option autoImplicit false

theorem mme_dwz_coarseAddress_selected_mode_words_postmap_eq_zero_of_coordinate
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
  sorry

-- Prove2me | Theorems.Thm_mme_dwz_step1_mixed_selected_address_map_zero_of_coordinate
-- name    : mme_dwz_step1_mixed_selected_address_map_zero_of_coordinate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-28T11:20:46.01654+00:00
-- url     : https://prove2.me/theorems/c7a33c92-653d-4772-8726-719bd1a93c8c
-- title:
--   A zero fine coordinate kills the selected mixed-address block
-- statement:
--   For the mixed coarse address built from competitor X/Y modes and the owner Z mode, one vanishing selected fine square-CW block annihilates the selected Step-1 postmaps on the entire graded address block.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6, Additional Zeroing-Out Step 1; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_step1_mixed_selected_full_map_data

open MME Module PiTensorProduct

universe u

set_option autoImplicit false

open MME.DWZSourceAligned
open MME.DWZStep1Support
open MME.DWZGlobalCorrelated

theorem mme_dwz_step1_mixed_selected_address_map_zero_of_coordinate
    {K : Type u} [Field K]
    (m : ℕ) {p N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (competitor owner : Fin n)
    (W : AddressZWord (sourceWord reindex edge owner))
    (x : AddressModeWord (sourceWord reindex edge competitor) 0)
    (y : AddressModeWord (sourceWord reindex edge competitor) 1)
    (r : Fin L)
    (hFineZero : (cwSquareFineSplitGrading K 6).blockTensor
      (fun i ↦ MME.DWZStep1Support.fineSplitGrade
        (![addressModeLeftGrade x r,
          addressModeLeftGrade y r,
          (W r).leftGrade] i)
        (![addressModeRightGrade x r,
          addressModeRightGrade y r,
          (W r).rightGrade] i)) = 0) :
    PiTensorProduct.map
      (step1MixedSelectedAddressMaps K m reindex q edge
        competitor owner W x y)
      (gradedAddressBlock (cwSquareCanonicalGrading K 6)
        (step1MixedAddress reindex edge competitor owner)).t = 0 := by
  sorry

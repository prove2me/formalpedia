-- Prove2me | Theorems.Thm_mme_dwz_step1_filtered_mixed_selected_map_zero_of_coordinate
-- name    : mme_dwz_step1_filtered_mixed_selected_map_zero_of_coordinate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-28T11:18:44.602677+00:00
-- url     : https://prove2.me/theorems/d639865c-8451-4797-98b8-9eed50c7e3e3
-- title:
--   One zero fine coordinate kills a selected mixed-owner map
-- statement:
--   A vanishing fine square-CW block in one coordinate annihilates the exact Step-1-filtered mixed-owner tensor map selected by accepted X/Y words and one canonical Z word.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6, Additional Zeroing-Out Step 1; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_step1_mixed_common_state_source_data

open MME Module PiTensorProduct

universe u

set_option autoImplicit false

open MME.DWZSourceAligned
open MME.DWZStep1Support
open MME.DWZGlobalCorrelated

theorem mme_dwz_step1_filtered_mixed_selected_map_zero_of_coordinate
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
      (step1FilteredMixedSelectedXYMaps K m reindex q edge
        competitor owner W x y)
      ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow L).t = 0 := by
  sorry

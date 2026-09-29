-- Prove2me | Theorems.Thm_mme_dwz_step1_mixed_selected_full_map_zero_of_coordinate
-- name    : mme_dwz_step1_mixed_selected_full_map_zero_of_coordinate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-28T11:19:53.07881+00:00
-- url     : https://prove2.me/theorems/0acaafe2-eb15-46c3-97ca-a172a7748cae
-- title:
--   One zero fine coordinate annihilates the selected mixed full-source maps
-- statement:
--   Choose canonical X and Y address words for one competitor and a canonical Z word for an owner. If the corresponding fine block vanishes at one source coordinate, then the tensor obtained by applying the selected Step-1-filtered mixed-owner maps to the full squared Coppersmith--Winograd power is zero. This transports the coordinate-local support obstruction through the mixed coarse-address projector without changing the selected maps.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6, Additional Zeroing-Out Step 1; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_step1_mixed_selected_full_map_data

open MME Module PiTensorProduct

universe u

set_option autoImplicit false

open MME.DWZSourceAligned
open MME.DWZStep1Support
open MME.DWZGlobalCorrelated

theorem mme_dwz_step1_mixed_selected_full_map_zero_of_coordinate
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
      (step1MixedSelectedFullMaps K m reindex q edge
        competitor owner W x y)
      ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow L).t = 0 := by
  sorry

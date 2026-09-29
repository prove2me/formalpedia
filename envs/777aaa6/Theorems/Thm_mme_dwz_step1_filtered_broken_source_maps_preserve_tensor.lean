-- Prove2me | Theorems.Thm_mme_dwz_step1_filtered_broken_source_maps_preserve_tensor
-- name    : mme_dwz_step1_filtered_broken_source_maps_preserve_tensor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-28T10:23:15.464042+00:00
-- url     : https://prove2.me/theorems/3ac4b125-d091-4f83-83c3-50fd7ff6b32a
-- title:
--   Step-1-filtered source maps preserve one broken owner
-- statement:
--   For one exact-profile owner, projecting the square CW power to its coarse address, applying the Additional Zeroing-Out Step 1 X/Y word filters, and applying the Step-2 surviving-Z mask preserves the literal broken address tensor.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6, Additional Zeroing-Out Steps 1 and 2; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_step1_broken_owner_maps

open MME Module PiTensorProduct
open MME.DWZSourceAligned

universe u

set_option autoImplicit false

theorem mme_dwz_step1_filtered_broken_source_maps_preserve_tensor
    {K : Type u} [Field K]
    (m : ℕ) {N : ℕ} (outer : Fin N → Fin 15)
    (copy : DWZSquare.BrokenBlockCopy
      (DWZTable2StandardForm.UsefulBlock m outer)) :
    PiTensorProduct.map
        (step1FilteredBrokenSourceMaps K m outer copy)
        ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow N).t =
      (brokenAddressObj K m outer copy).t := by
  sorry

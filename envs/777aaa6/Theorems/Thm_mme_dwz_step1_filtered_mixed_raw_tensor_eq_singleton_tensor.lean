-- Prove2me | Theorems.Thm_mme_dwz_step1_filtered_mixed_raw_tensor_eq_singleton_tensor
-- name    : mme_dwz_step1_filtered_mixed_raw_tensor_eq_singleton_tensor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-28T10:29:56.357304+00:00
-- url     : https://prove2.me/theorems/922747de-8a50-472d-90a4-90f2f324835d
-- title:
--   Raw post-projection tensor equals the literal singleton tensor
-- statement:
--   The generic post-projection presentation of the Step-1 mixed-owner map has exactly the same tensor value as the literal filtered singleton source-map family.
-- source:
--   Formal tensor-map normalization for Duan--Wu--Zhou Additional Zeroing-Out Step 1, arXiv:2210.10173v5, Section 6.

import Definitions.Def_mme_dwz_step1_mixed_common_state_source_data

open MME PiTensorProduct

universe u

set_option autoImplicit false

open MME.DWZGlobalCorrelated

theorem mme_dwz_step1_filtered_mixed_raw_tensor_eq_singleton_tensor
    {K : Type u} [Field K]
    (m : ℕ) {p N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (competitor owner : Fin n)
    (W : MME.DWZSourceAligned.AddressZWord
      (sourceWord reindex edge owner)) :
    step1FilteredMixedRawTensor K m reindex q edge competitor owner W =
      PiTensorProduct.map
        (step1FilteredMixedSingletonMaps K m reindex q edge
          competitor owner W)
        ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow L).t := by
  sorry

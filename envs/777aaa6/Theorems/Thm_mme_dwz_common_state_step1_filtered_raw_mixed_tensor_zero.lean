-- Prove2me | Theorems.Thm_mme_dwz_common_state_step1_filtered_raw_mixed_tensor_zero
-- name    : mme_dwz_common_state_step1_filtered_raw_mixed_tensor_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-28T11:00:22.769333+00:00
-- url     : https://prove2.me/theorems/27d3a69e-d76d-4ea3-bec6-d9a98a918cbc
-- title:
--   Common-state Step-1 raw mixed tensor vanishes
-- statement:
--   For two distinct owners retained in one canonical affine state, a surviving Z word and the selected-word fine-support property force the raw Step-1-filtered mixed tensor to vanish.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6, Claims 6.2 and 6.8; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_step1_mixed_common_state_source_data
import Definitions.Def_mme_dwz_table2_affine_hash_bucket

open MME PiTensorProduct

universe u

set_option autoImplicit false

open MME.DWZSourceAligned
open MME.DWZGlobalCorrelated

theorem mme_dwz_common_state_step1_filtered_raw_mixed_tensor_zero
    {K : Type u} [Field K]
    (m : ℕ) {p N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (hpodd : Odd p)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ))
    (A : Finset (Fin (N + 1) → Fin 15))
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (hBucket : ∀ j, edge j ∈ dwzTable2AffineHashBucket S A q)
    (competitor owner : Fin n) (hne : competitor ≠ owner)
    (W : AddressZWord (sourceWord reindex edge owner))
    (hSurvives : addressWordSurvives m
      (sourceWord reindex edge owner)
      (commonStateBrokenCopy m reindex q edge owner) W)
    (hSelectedSupport : Step1MixedSelectedSupportProperty
      K m reindex q edge competitor owner W) :
    step1FilteredMixedRawTensor K m reindex q edge
      competitor owner W = 0 := by
  sorry

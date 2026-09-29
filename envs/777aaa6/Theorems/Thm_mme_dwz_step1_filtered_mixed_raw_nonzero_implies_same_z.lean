-- Prove2me | Theorems.Thm_mme_dwz_step1_filtered_mixed_raw_nonzero_implies_same_z
-- name    : mme_dwz_step1_filtered_mixed_raw_nonzero_implies_same_z
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-28T10:42:52.80328+00:00
-- url     : https://prove2.me/theorems/c530dbb8-0c0a-47ed-95c8-36c092220406
-- title:
--   Nonzero Step-1 mixed raw tensor forces a common coarse-Z word
-- statement:
--   For a common X/Y competitor, a Z owner, and one selected Z word in a shared affine state, nonvanishing of the raw Step-1-filtered mixed tensor forces the owner and competitor source words to have identical coarse-Z shape at every coordinate.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6, Additional Zeroing-Out Step 1 and Claim 6.2; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_step1_mixed_common_state_source_data
import Theorems.Thm_mme_dwz_mixed_coarse_postmap_nonzero_implies_same_z_of_xy_owner

open MME PiTensorProduct

universe u

set_option autoImplicit false

open MME.DWZSourceAligned
open MME.DWZGlobalCorrelated

theorem mme_dwz_step1_filtered_mixed_raw_nonzero_implies_same_z
    {K : Type u} [Field K]
    (m : ℕ) {p N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (competitor owner : Fin n)
    (W : AddressZWord (sourceWord reindex edge owner))
    (hRaw : Step1FilteredMixedRawNonzero
      K m reindex q edge competitor owner W) :
    ∀ r,
      MME.DWZSquare.shapeZ (sourceWord reindex edge owner r) =
        MME.DWZSquare.shapeZ (sourceWord reindex edge competitor r) := by
  sorry

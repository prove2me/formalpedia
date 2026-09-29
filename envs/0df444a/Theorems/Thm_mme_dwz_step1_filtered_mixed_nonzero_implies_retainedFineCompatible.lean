-- Prove2me | Theorems.Thm_mme_dwz_step1_filtered_mixed_nonzero_implies_retainedFineCompatible
-- name    : mme_dwz_step1_filtered_mixed_nonzero_implies_retainedFineCompatible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-28T10:44:57.036819+00:00
-- url     : https://prove2.me/theorems/3d1c2b0d-1202-48da-b3de-df12cdbd0a44
-- title:
--   Nonzero Step-1 mixed singleton yields retained fine compatibility
-- statement:
--   For a common X/Y competitor, a Z owner, and one selected useful Z word, assume the owner and competitor have the same coarse-Z word and that every nonzero accepted selected X/Y singleton exposes coordinatewise fine support. If the complete Step-1-filtered mixed singleton is nonzero, then the selected useful Z block is fine-compatible with the competitor in the exact retained sense used by Claim 6.8.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6, Additional Zeroing-Out Step 1 and Claims 6.2 and 6.8; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_step1_mixed_fine_callback_predicates

open MME Module PiTensorProduct

universe u


set_option autoImplicit false

open MME.DWZSourceAligned
open MME.DWZGlobalCorrelated

theorem mme_dwz_step1_filtered_mixed_nonzero_implies_retainedFineCompatible
    {K : Type u} [Field K]
    (m : ℕ) {p N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (competitor owner : Fin n)
    (W : AddressZWord (sourceWord reindex edge owner)) :
    Step1FilteredMixedFineCompatibilityProperty
      K m reindex q edge competitor owner W := by
  sorry

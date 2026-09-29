-- Prove2me | Theorems.Thm_mme_dwz_step1_filtered_mixed_fine_callback
-- name    : mme_dwz_step1_filtered_mixed_fine_callback
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-28T10:56:38.532795+00:00
-- url     : https://prove2.me/theorems/e48da9dd-aa37-4ac5-9d9c-d8dced8979b7
-- title:
--   The Step-1 mixed-owner maps supply the Claim-6.8 fine callback
-- statement:
--   For a common X/Y competitor, a Z owner, and one selected Z word, assume the selected accepted X/Y singleton maps expose coordinatewise fine support. If the raw common-state mixed tensor is nonzero, then every useful realization of the selected Z word is fine-compatible with the competitor in the precise sense required by Claim 6.8. Equivalently, the selected-support hypothesis supplies the fine-incidence callback consumed by the mixed-owner collision theorem.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6, Claims 6.2 and 6.8; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_step1_mixed_fine_callback_predicates

open MME PiTensorProduct

universe u

set_option autoImplicit false

open MME.DWZSourceAligned
open MME.DWZGlobalCorrelated

theorem mme_dwz_step1_filtered_mixed_fine_callback
    {K : Type u} [Field K]
    (m : ℕ) {p N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (competitor owner : Fin n)
    (W : AddressZWord (sourceWord reindex edge owner)) :
    Step1FilteredMixedFineCallbackProperty
      K m reindex q edge competitor owner W := by
  sorry

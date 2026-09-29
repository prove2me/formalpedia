-- Prove2me | Theorems.Thm_mme_dwz_step1_mixed_selected_support_property
-- name    : mme_dwz_step1_mixed_selected_support_property
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-28T11:19:06.402562+00:00
-- url     : https://prove2.me/theorems/a8f732c5-3252-41ac-8678-f199dfc61d35
-- title:
--   Selected Step-1 mixed-owner words have fine support
-- statement:
--   The accepted X/Y word singletons selected in the mixed-owner Step-1 construction have nonzero fine square-Coppersmith--Winograd support in every coordinate whenever their filtered mixed tensor is nonzero. This is the exact support predicate consumed by the mixed singleton-cross restriction.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6, Additional Zeroing-Out Step 1 and Claim 6.2; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_step1_mixed_common_state_source_data

open MME Module

universe u

set_option autoImplicit false

open MME.DWZSourceAligned
open MME.DWZGlobalCorrelated

theorem mme_dwz_step1_mixed_selected_support_property
    {K : Type u} [Field K]
    (m : ℕ) {p N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (competitor owner : Fin n)
    (W : AddressZWord (sourceWord reindex edge owner)) :
    Step1MixedSelectedSupportProperty
      K m reindex q edge competitor owner W := by
  sorry

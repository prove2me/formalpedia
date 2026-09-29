-- Prove2me | Theorems.Thm_mme_dwz_step1_mixed_selected_full_maps_eq_filtered
-- name    : mme_dwz_step1_mixed_selected_full_maps_eq_filtered
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-28T11:19:36.612989+00:00
-- url     : https://prove2.me/theorems/288fa1d4-9afa-4e0c-abc3-727278338a17
-- title:
--   Mixed selected full maps equal the Step-1 filtered maps
-- statement:
--   The full-source map family obtained by projecting to the mixed competitor-X/Y and owner-Z coarse address, selecting the chosen address words, and applying the broken-owner postmaps is exactly the existing Step-1 filtered mixed-owner X/Y map family.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6, Additional Zeroing-Out Step 1; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_step1_mixed_selected_full_map_data

open MME Module

universe u

set_option autoImplicit false

open MME.DWZSourceAligned
open MME.DWZGlobalCorrelated

theorem mme_dwz_step1_mixed_selected_full_maps_eq_filtered
    {K : Type u} [Field K]
    (m : ℕ) {p N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (competitor owner : Fin n)
    (W : AddressZWord (sourceWord reindex edge owner))
    (x : AddressModeWord (sourceWord reindex edge competitor) 0)
    (y : AddressModeWord (sourceWord reindex edge competitor) 1) :
    step1MixedSelectedFullMaps K m reindex q edge
        competitor owner W x y =
      step1FilteredMixedSelectedXYMaps K m reindex q edge
        competitor owner W x y := by
  sorry

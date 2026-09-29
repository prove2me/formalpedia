-- Prove2me | Theorems.Thm_mme_dwz_step1FilteredMixedSingletonMaps_eq_sourceFamily_apply
-- name    : mme_dwz_step1FilteredMixedSingletonMaps_eq_sourceFamily_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-28T11:11:58.30994+00:00
-- url     : https://prove2.me/theorems/0a2d8c38-f374-4bb2-b4d4-83208c8e9dae
-- title:
--   Mixed-singleton maps equal source-family maps pointwise
-- statement:
--   At each of the three tensor modes, the mixed-owner Step-1 singleton map is exactly the corresponding ordinary source-family map, with the surviving Z-word singleton inserted in mode two.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6, Additional Zeroing-Out Steps 1 and 2; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_step1_mixed_common_state_source_data

open MME Module

universe u

set_option autoImplicit false

open MME.DWZSourceAligned
open MME.DWZGlobalCorrelated

theorem mme_dwz_step1FilteredMixedSingletonMaps_eq_sourceFamily_apply
    {K : Type u} [Field K]
    (m : ℕ) {p N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (competitor owner : Fin n)
    (W : AddressZWord (sourceWord reindex edge owner))
    (i : Fin 3) :
    step1FilteredMixedSingletonMaps K m reindex q edge
        competitor owner W i =
      step1MixedSourceFamilySingletonMaps K m reindex q edge
        competitor owner W i := by
  sorry

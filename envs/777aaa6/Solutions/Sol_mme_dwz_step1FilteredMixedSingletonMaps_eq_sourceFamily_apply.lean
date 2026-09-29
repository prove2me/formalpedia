-- Prove2me | solution 1 for mme_dwz_step1FilteredMixedSingletonMaps_eq_sourceFamily_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-28T11:12:31.175718+00:00
-- url     : https://prove2.me/submissions/105be4d0-4ee4-4f8d-afcb-4383a37bd398

import Definitions.Def_mme_dwz_step1_mixed_common_state_source_data
import Theorems.Thm_mme_dwz_step1MixedCoarseProj_eq_owner_gradedAddressProj

open MME Module

universe u

set_option autoImplicit false
set_option warningAsError true

open MME.DWZSourceAligned
open MME.DWZGlobalCorrelated

theorem solution
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
  fin_cases i
  · unfold step1FilteredMixedSingletonMaps
    unfold step1FilteredMixedSingletonAddressPost
    rw [Function.update_of_ne (by decide)]
    unfold step1MixedSourceFamilySingletonMaps
    rw [Function.update_of_ne (by decide)]
    unfold step1FilteredBrokenSourceMaps
    rw [mme_dwz_step1MixedCoarseProj_eq_owner_gradedAddressProj]
    rfl
  · unfold step1FilteredMixedSingletonMaps
    unfold step1FilteredMixedSingletonAddressPost
    rw [Function.update_of_ne (by decide)]
    unfold step1MixedSourceFamilySingletonMaps
    rw [Function.update_of_ne (by decide)]
    unfold step1FilteredBrokenSourceMaps
    rw [mme_dwz_step1MixedCoarseProj_eq_owner_gradedAddressProj]
    rfl
  · classical
    change step1FilteredMixedSingletonMaps K m reindex q edge
        competitor owner W (2 : Fin 3) =
      step1MixedSourceFamilySingletonMaps K m reindex q edge
        competitor owner W (2 : Fin 3)
    unfold step1FilteredMixedSingletonMaps
    unfold step1FilteredMixedSingletonAddressPost
    rw [Function.update_self]
    unfold step1MixedSourceFamilySingletonMaps
    rw [Function.update_self]
    unfold step1FilteredBrokenAddressMaps addressStep1Projector
    rw [mme_dwz_step1MixedCoarseProj_eq_owner_gradedAddressProj]
    rfl

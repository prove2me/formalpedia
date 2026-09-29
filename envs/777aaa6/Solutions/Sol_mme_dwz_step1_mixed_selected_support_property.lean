-- Prove2me | solution 1 for mme_dwz_step1_mixed_selected_support_property
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-28T11:23:00.199298+00:00
-- url     : https://prove2.me/submissions/b945e07f-47a0-43a2-bdee-7f661606e4f5

import Definitions.Def_mme_dwz_step1_mixed_common_state_source_data
import Theorems.Thm_mme_dwz_step1_filtered_mixed_selected_map_zero_of_coordinate

open MME Module PiTensorProduct

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
    (W : AddressZWord (sourceWord reindex edge owner)) :
    Step1MixedSelectedSupportProperty
      K m reindex q edge competitor owner W := by
  classical
  intro x _hx y _hy hNonzero r hFineZero
  apply hNonzero
  exact mme_dwz_step1_filtered_mixed_selected_map_zero_of_coordinate
    m reindex q edge competitor owner W x y r hFineZero

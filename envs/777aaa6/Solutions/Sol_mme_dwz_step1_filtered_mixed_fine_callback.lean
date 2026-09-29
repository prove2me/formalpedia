-- Prove2me | solution 1 for mme_dwz_step1_filtered_mixed_fine_callback
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-28T10:57:06.938519+00:00
-- url     : https://prove2.me/submissions/5c036504-6e49-4943-9ebb-71fb121fe689

import Definitions.Def_mme_dwz_step1_mixed_fine_callback_predicates
import Theorems.Thm_mme_dwz_step1_filtered_mixed_raw_tensor_eq_singleton_tensor
import Theorems.Thm_mme_dwz_step1_filtered_mixed_raw_nonzero_implies_same_z
import Theorems.Thm_mme_dwz_step1_filtered_mixed_nonzero_implies_retainedFineCompatible

open MME PiTensorProduct

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
    Step1FilteredMixedFineCallbackProperty
      K m reindex q edge competitor owner W := by
  unfold Step1FilteredMixedFineCallbackProperty
  intro hSelectedSupport hRaw hUseful
  have hSameZ := mme_dwz_step1_filtered_mixed_raw_nonzero_implies_same_z
    m reindex q edge competitor owner W hRaw
  have hTensor :=
    mme_dwz_step1_filtered_mixed_raw_tensor_eq_singleton_tensor (K := K)
      m reindex q edge competitor owner W
  have hFiltered : Step1FilteredMixedSingletonNonzero
      K m reindex q edge competitor owner W := by
    unfold Step1FilteredMixedRawNonzero at hRaw
    unfold Step1FilteredMixedSingletonNonzero
    rw [hTensor] at hRaw
    exact hRaw
  exact mme_dwz_step1_filtered_mixed_nonzero_implies_retainedFineCompatible
    m reindex q edge competitor owner W hSameZ hSelectedSupport hUseful
      hFiltered

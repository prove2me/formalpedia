-- Prove2me | solution 1 for mme_dwz_common_state_step1_filtered_raw_mixed_tensor_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-28T11:01:25.918687+00:00
-- url     : https://prove2.me/submissions/2611887a-761e-479f-bb01-228e30a6edd5

import Definitions.Def_mme_dwz_step1_mixed_common_state_source_data
import Definitions.Def_mme_dwz_table2_affine_hash_bucket
import Theorems.Thm_mme_dwz_step1_filtered_mixed_fine_callback
import Theorems.Thm_mme_dwz_common_state_mixed_singleton_zero_of_fine_compatible

open MME PiTensorProduct

universe u
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
set_option maxRecDepth 10000

open MME.DWZSourceAligned
open MME.DWZGlobalCorrelated

theorem solution
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
  let js := step1MixedOwnerIndex competitor owner
  let post := step1FilteredMixedSingletonPost K m reindex q edge
    competitor owner W
  have h01 : js 0 = js 1 := rfl
  have h02 : js 0 ≠ js 2 := by
    simpa only [js, step1MixedOwnerIndex] using hne
  have hCallback := mme_dwz_step1_filtered_mixed_fine_callback
    m reindex q edge competitor owner W hSelectedSupport
  unfold Step1FilteredMixedRawNonzero at hCallback
  unfold step1FilteredMixedRawTensor step1FilteredMixedRawMaps
  exact mme_dwz_common_state_mixed_singleton_zero_of_fine_compatible
    m reindex hpodd S hSrange hSfree A q edge hBucket js h01 h02 W
      hSurvives post (by
        dsimp only
        intro hRaw hUseful
        exact hCallback hRaw hUseful)

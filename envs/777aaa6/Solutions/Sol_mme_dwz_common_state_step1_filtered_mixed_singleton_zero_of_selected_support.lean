-- Prove2me | solution 1 for mme_dwz_common_state_step1_filtered_mixed_singleton_zero_of_selected_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-28T11:10:05.815362+00:00
-- url     : https://prove2.me/submissions/142a44b1-e4e0-43fd-be3e-77de4c761569

import Definitions.Def_mme_dwz_step1_mixed_common_state_source_data
import Definitions.Def_mme_dwz_table2_affine_hash_bucket
import Theorems.Thm_mme_dwz_common_state_step1_filtered_raw_mixed_tensor_zero
import Theorems.Thm_mme_dwz_step1_filtered_mixed_raw_tensor_eq_singleton_tensor

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
    PiTensorProduct.map
        (step1FilteredMixedSingletonMaps K m reindex q edge
          competitor owner W)
        ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow L).t = 0 := by
  have hRaw := mme_dwz_common_state_step1_filtered_raw_mixed_tensor_zero
    m reindex hpodd S hSrange hSfree A q edge hBucket competitor owner hne W
      hSurvives hSelectedSupport
  have hTensor :=
    mme_dwz_step1_filtered_mixed_raw_tensor_eq_singleton_tensor (K := K)
      m reindex q edge competitor owner W
  rw [← hTensor]
  exact hRaw

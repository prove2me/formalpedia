-- Prove2me | Theorems.Thm_mme_dwz_common_state_step1_filtered_mixed_singleton_zero_of_selected_support
-- name    : mme_dwz_common_state_step1_filtered_mixed_singleton_zero_of_selected_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-28T11:09:38.688067+00:00
-- url     : https://prove2.me/theorems/fb2c1ef1-0c2d-42b6-a224-4daf54a042a3
-- title:
--   Selected Step-1 support kills a distinct mixed Z owner
-- statement:
--   For owners in one canonical affine bucket and one shared affine state, a surviving Z-word singleton annihilates a distinct mixed Z owner once the selected accepted X/Y words expose their coordinatewise fine support.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6, Claim 6.2 and Claim 6.8; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_step1_mixed_common_state_source_data
import Definitions.Def_mme_dwz_table2_affine_hash_bucket

open MME PiTensorProduct

universe u

set_option autoImplicit false

open MME.DWZSourceAligned
open MME.DWZGlobalCorrelated

theorem mme_dwz_common_state_step1_filtered_mixed_singleton_zero_of_selected_support
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
  sorry

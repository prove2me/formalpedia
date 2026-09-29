-- Prove2me | solution 1 for mme_dwz_step1_filtered_mixed_raw_nonzero_implies_same_z
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-28T10:43:10.018534+00:00
-- url     : https://prove2.me/submissions/1728552a-793e-4ef9-9b96-a8be4ddb065b

import Definitions.Def_mme_dwz_step1_mixed_common_state_source_data
import Theorems.Thm_mme_dwz_mixed_coarse_postmap_nonzero_implies_same_z_of_xy_owner

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
    (W : AddressZWord (sourceWord reindex edge owner))
    (hRaw : Step1FilteredMixedRawNonzero
      K m reindex q edge competitor owner W) :
    ∀ r,
      MME.DWZSquare.shapeZ (sourceWord reindex edge owner r) =
        MME.DWZSquare.shapeZ (sourceWord reindex edge competitor r) := by
  let outer : Fin n → Fin L → Fin 15 := sourceWord reindex edge
  let js := step1MixedOwnerIndex competitor owner
  let post := step1FilteredMixedSingletonPost K m reindex q edge
    competitor owner W
  unfold Step1FilteredMixedRawNonzero step1FilteredMixedRawTensor
    step1FilteredMixedRawMaps at hRaw
  have h := mme_dwz_mixed_coarse_postmap_nonzero_implies_same_z_of_xy_owner
    outer js (by rfl) post hRaw
  intro r
  simpa only [outer, js, step1MixedOwnerIndex, Matrix.cons_val_zero,
    Matrix.cons_val_two] using (h r).symm

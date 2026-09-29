-- Prove2me | Theorems.Thm_mme_dwz_common_state_hash_retained_of_bucket_same_z
-- name    : mme_dwz_common_state_hash_retained_of_bucket_same_z
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T19:50:55.69835+00:00
-- url     : https://prove2.me/theorems/d55ad6f4-b54f-43e0-8be6-542a8528786d
-- title:
--   Canonical-bucket owners with the same coarse Z satisfy the common-state hash
-- statement:
--   Let an AP-free canonical affine bucket contain a family of Table-2 component words. If two owners in the family have the same complete coarse-Z word, then the competitor's X hash equals the distinguished owner's Z hash at the very same affine state q. Thus they satisfy the common-state hash predicate used by the correlated broken copy.

import Definitions.Def_mme_dwz_global_common_state_broken_copy
import Theorems.Thm_mme_dwz_asymmetric_hash_AP_free_membership_iff_common_label

open MME
open MME.DWZGlobalCorrelated

set_option autoImplicit false

theorem mme_dwz_common_state_hash_retained_of_bucket_same_z
    {p N n : ℕ} (hpodd : Odd p)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ))
    (A : Finset (Fin (N + 1) → Fin 15))
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (hBucket : ∀ j, edge j ∈ dwzTable2AffineHashBucket S A q)
    (owner competitor : Fin n)
    (hSameZ : sameCoarseZ edge owner competitor) :
    commonStateHashRetained q edge owner competitor := by
  sorry

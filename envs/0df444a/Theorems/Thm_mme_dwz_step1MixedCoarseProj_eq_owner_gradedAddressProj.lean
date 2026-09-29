-- Prove2me | Theorems.Thm_mme_dwz_step1MixedCoarseProj_eq_owner_gradedAddressProj
-- name    : mme_dwz_step1MixedCoarseProj_eq_owner_gradedAddressProj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-28T10:34:47.054068+00:00
-- url     : https://prove2.me/theorems/c09eced2-6b81-4da5-af8b-874fa95aff8c
-- title:
--   Mixed coarse projection equals the owner's ordinary projection
-- statement:
--   In each mode, composing the canonical equality transport from a mixed coarse address with its graded-address projection is exactly the ordinary coarse-address projection for that mode's owner.
-- source:
--   Formal address-transport normalization for Duan--Wu--Zhou Additional Zeroing-Out Step 1, arXiv:2210.10173v5, Section 6.

import Definitions.Def_mme_dwz_step1_mixed_common_state_source_data

open MME Module

universe u

set_option autoImplicit false

open MME.DWZSourceAligned
open MME.DWZGlobalCorrelated

theorem mme_dwz_step1MixedCoarseProj_eq_owner_gradedAddressProj
    {K : Type u} [Field K] {N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (competitor owner : Fin n) (i : Fin 3) :
    step1MixedCoarseProj K reindex edge competitor owner i =
      gradedAddressProj (cwSquareCanonicalGrading K 6) L
        (coarseAddress
          (sourceWord reindex edge
            (step1MixedOwnerIndex competitor owner i))) i := by
  sorry

-- Prove2me | Theorems.Thm_mme_dwz_step1MixedModeEquiv_apply_arbitraryCoarseAddressModeBasis
-- name    : mme_dwz_step1MixedModeEquiv_apply_arbitraryCoarseAddressModeBasis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-28T11:39:13.546616+00:00
-- url     : https://prove2.me/theorems/43ad61c3-6bc4-4a03-9c7e-c26debf004a0
-- title:
--   Mixed-mode address equivalence preserves canonical basis labels
-- statement:
--   For the mixed Step-1 address with competitor-owned X and Y modes and an owner-owned Z mode, the canonical mode equivalence to the corresponding owner's ordinary coarse-address block sends every canonical mixed-address basis word to the owner-address basis word with the same label.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6, Additional Zeroing-Out Step 1; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_step1_mixed_selected_full_map_data

open MME Module

universe u

set_option autoImplicit false

open MME.DWZSourceAligned
open MME.DWZGlobalCorrelated

theorem mme_dwz_step1MixedModeEquiv_apply_arbitraryCoarseAddressModeBasis
    {K : Type u} [Field K] {N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (competitor owner : Fin n) (i : Fin 3)
    (word : AddressModeWord
      (sourceWord reindex edge
        (step1MixedOwnerIndex competitor owner i)) i) :
    step1MixedModeEquiv K reindex edge competitor owner i
        (arbitraryCoarseAddressModeBasis K
          (step1MixedAddress reindex edge competitor owner) i word) =
      coarseAddressModeBasis K
        (sourceWord reindex edge
          (step1MixedOwnerIndex competitor owner i)) i word := by
  sorry

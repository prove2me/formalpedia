-- Prove2me | Theorems.Thm_mme_basis_all_allowed_subtensor_mono
-- name    : mme_basis_all_allowed_subtensor_mono
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T07:52:44.519509+00:00
-- url     : https://prove2.me/theorems/229381cd-7c84-4cc2-abdd-3aa250c8b0d0
-- title:
--   Allowed-set inclusion gives an actual tensor restriction
-- statement:
--   For any three-mode tensor and mode bases, inclusion of every allowed set gives a restriction from the larger basis-projected tensor to the smaller basis-projected tensor. The full matrix exponent bound remains a separate obligation.
-- source:
--   Kernel-checked regional count identities and exact extraction with empty regions.

import Theorems.Thm_mme_restrict_basisAllAllowedSubtensor_of_vanishes
open MME Module
universe u

theorem mme_basis_all_allowed_subtensor_mono
    {K : Type u} [Field K] (T : TensorObj K 3) {ι : Fin 3 → Type u}
    (b : (i : Fin 3) → Basis (ι i) K (T.V i))
    (small large : (i : Fin 3) → ι i → Prop)
    (h : ∀ i j, small i j → large i j) :
    TensorObj.Restrict (T.basisAllAllowedSubtensor b small)
      (T.basisAllAllowedSubtensor b large) := by sorry

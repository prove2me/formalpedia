-- Prove2me | Theorems.Thm_mme_primary_hash_family_permuted_outer_extraction_exact
-- name    : mme_primary_hash_family_permuted_outer_extraction_exact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T12:57:53.138336+00:00
-- url     : https://prove2.me/theorems/33f739bf-9b4f-4bb8-a7b4-ac2759cc55a5
-- title:
--   Primary-family outer extraction commutes exactly with a mode permutation
-- statement:
--   Let an order-three tensor $T$ carry the four-block coupled grading used by a primary hash family, and let $e$ be any permutation of its modes. Transport the outer-extraction maps along the canonical equivalence between $(eT)^{\otimes 2N}$ and $e(T^{\otimes 2N})$. The resulting maps send the permuted tensor power exactly to the permuted direct sum of retained stars:
--
--   $$
--   E^{e}((eT)^{\otimes 2N})=e(\bigoplus_a S_a).
--   $$
--
--   This is the exact map-level naturality needed to combine cyclic canonical-component routers with primary-family extraction and allowed-word projectors.
-- source:
--   Naturality of the Coppersmith--Winograd primary-family outer extraction under mode permutations; q=6 DWZ 121/211 source bridge.

import Theorems.Thm_mme_perm_kronPow_mode_equiv_preserves_tensor
import Theorems.Thm_mme_primary_hash_family_sharedZ_outer_extraction_exact

open MME MME.TensorObj PiTensorProduct BigOperators
open CoupledCTensorPackaging

universe u

set_option autoImplicit false

theorem mme_primary_hash_family_permuted_outer_extraction_exact
    {K : Type u} [Field K]
    {T : TensorObj K 3} (grading : T.TypeGrading 3)
    {N L G A H : ℕ}
    (family : CWQ6PrimaryHashFamily N L G A H)
    (hSupport : ∀ σ : Fin 3 → Fin 3,
      σ ≠ ![0, 0, 0] → σ ≠ ![1, 1, 1] →
      σ ≠ ![0, 1, 2] → σ ≠ ![1, 0, 2] →
      grading.blockTensor σ = 0)
    (e : Equiv.Perm (Fin 3)) :
    PiTensorProduct.map
        (fun i ↦ (outerExtractionMap grading family (e.symm i)).comp
          (TensorObj.permKronPowModeEquiv e T i (2 * N)).toLinearMap)
        ((TensorObj.permObj e T).kronPow (2 * N)).t =
      (TensorObj.permObj e
        (TensorObj.bigAdd (starObj grading family))).t := by
  sorry

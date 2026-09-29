-- Prove2me | Theorems.Thm_mme_dwz_q6_canonical_121_swap_to_211_basis_transport
-- name    : mme_dwz_q6_canonical_121_swap_to_211_basis_transport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T12:12:49.656676+00:00
-- url     : https://prove2.me/theorems/c4245627-ec29-43e1-8de6-72c3b1b4f6ab
-- title:
--   Exact mode-swap transport from the q=6 121 component to 211
-- statement:
--   Swapping the first two tensor modes carries the literal q=6 Table-2 121 component to the literal 211 component. The same explicit modewise maps preserve the component tensor exactly and fix every named third-mode coarse-pair basis label.
-- source:
--   Duan, Wu, and Zhou, arXiv:2210.10173v5, Section 6.3 and Table 2; symmetry of the Coppersmith--Winograd square under exchanging X and Y.

import Definitions.Def_mme_dwz_component_word_projection
import Definitions.Def_mme_six_symmetrized_tau_value

open MME MME.TensorObj MME.DWZComponentRestriction PiTensorProduct

universe u

set_option autoImplicit false

theorem mme_dwz_q6_canonical_121_swap_to_211_basis_transport
    (K : Type u) [Field K] :
    ∃ maps : ∀ i : Fin 3,
        (TensorObj.permObj swapFirstTwoPerm
          (canonicalComponentBlock K (13 : Fin 15))).V i →ₗ[K]
        (canonicalComponentBlock K (14 : Fin 15)).V i,
      PiTensorProduct.map maps
          (TensorObj.permObj swapFirstTwoPerm
            (canonicalComponentBlock K (13 : Fin 15))).t =
        (canonicalComponentBlock K (14 : Fin 15)).t ∧
      ∀ p : LiftedCoarsePair.{u} 6 1,
        maps 2 (canonicalComponentZBasis K (13 : Fin 15) p) =
          canonicalComponentZBasis K (14 : Fin 15) p := by
  sorry

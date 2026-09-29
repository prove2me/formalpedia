-- Prove2me | Theorems.Thm_mme_dwz_q6_canonical_211_swap_to_121_basis_transport
-- name    : mme_dwz_q6_canonical_211_swap_to_121_basis_transport
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T01:23:26.096163+00:00
-- url     : https://prove2.me/theorems/6990348c-6372-4a5c-8ab8-393f04b94926
-- title:
--   Swapped canonical 211 maps to 121 preserving Z-basis labels
-- statement:
--   Over every field $K$, the canonical 211 component with its first two tensor modes swapped admits mode maps to the canonical 121 component that preserve the tensor. On the third mode these maps preserve every named coarse-pair basis label:
--   $$F_2(b_{211}(p))=b_{121}(p).$$
--   This is the reverse-direction basis transport needed to connect the literal paired 211 source to the canonical 121/211 routing construction.
-- source:
--   Reverse orientation of the accepted mme_dwz_q6_canonical_121_swap_to_211_basis_transport construction. The explicit Coppersmith–Winograd square swap preserves the tensor and every coarse basis grade; its restriction swaps the 211 and 121 blocks.

import Definitions.Def_mme_dwz_component_word_projection
import Definitions.Def_mme_six_symmetrized_tau_value
open MME MME.DWZComponentRestriction Module TensorProduct PiTensorProduct
universe u
set_option autoImplicit false

theorem mme_dwz_q6_canonical_211_swap_to_121_basis_transport
    (K : Type u) [Field K] :
    ∃ maps : ∀ i : Fin 3,
        (TensorObj.permObj swapFirstTwoPerm
          (canonicalComponentBlock K (14 : Fin 15))).V i →ₗ[K]
        (canonicalComponentBlock K (13 : Fin 15)).V i,
      PiTensorProduct.map maps
          (TensorObj.permObj swapFirstTwoPerm
            (canonicalComponentBlock K (14 : Fin 15))).t =
        (canonicalComponentBlock K (13 : Fin 15)).t ∧
      ∀ p : LiftedCoarsePair.{u} 6 1,
        maps 2 (canonicalComponentZBasis K (14 : Fin 15) p) =
          canonicalComponentZBasis K (13 : Fin 15) p := by sorry

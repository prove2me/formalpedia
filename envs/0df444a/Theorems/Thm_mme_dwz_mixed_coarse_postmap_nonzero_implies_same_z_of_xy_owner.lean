-- Prove2me | Theorems.Thm_mme_dwz_mixed_coarse_postmap_nonzero_implies_same_z_of_xy_owner
-- name    : mme_dwz_mixed_coarse_postmap_nonzero_implies_same_z_of_xy_owner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T20:17:05.348819+00:00
-- url     : https://prove2.me/theorems/0e5e9c09-18a6-4ab2-802c-4cf81fbf7520
-- title:
--   A supported mixed coarse block with one XY owner has the same Z word
-- statement:
--   Take a mixed coarse-address block in a power of the squared Coppersmith–Winograd tensor. If the X and Y modes come from the same owner and the block remains nonzero after arbitrary modewise postprocessing, then at every coordinate the Z shape of that common X/Y owner equals the Z shape selected by the Z-mode owner. Equivalently, the two owners have the same complete coarse-Z word.

import Theorems.Thm_mme_gradedAddressProj_then_post_map_eq_zero_of_coordinate
import Theorems.Thm_mme_CW_square_canonical_support_and_scalar_blocks
import Definitions.Def_mme_dwz_source_aligned_broken_obj

open MME PiTensorProduct

universe u

set_option autoImplicit false

theorem mme_dwz_mixed_coarse_postmap_nonzero_implies_same_z_of_xy_owner
    {K : Type u} [Field K] {N k : ℕ}
    (outer : Fin k → Fin N → Fin 15)
    (js : Fin 3 → Fin k) (h01 : js 0 = js 1)
    {W : Fin 3 → Type u}
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (post : ∀ i : Fin 3,
      (gradedAddressBlock (cwSquareCanonicalGrading K 6)
        (fun i r ↦ MME.DWZSourceAligned.coarseAddress
          (outer (js i)) i r)).V i →ₗ[K] W i)
    (hNonzero :
      PiTensorProduct.map
          (fun i ↦ (post i).comp
            (gradedAddressProj (cwSquareCanonicalGrading K 6) N
              (fun i r ↦ MME.DWZSourceAligned.coarseAddress
                (outer (js i)) i r) i))
          ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow N).t ≠ 0) :
    ∀ r,
      MME.DWZSquare.shapeZ (outer (js 0) r) =
        MME.DWZSquare.shapeZ (outer (js 2) r) := by
  sorry

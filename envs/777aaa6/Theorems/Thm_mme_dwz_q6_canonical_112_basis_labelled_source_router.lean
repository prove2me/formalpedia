-- Prove2me | Theorems.Thm_mme_dwz_q6_canonical_112_basis_labelled_source_router
-- name    : mme_dwz_q6_canonical_112_basis_labelled_source_router
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T06:45:42.067382+00:00
-- url     : https://prove2.me/theorems/ebc2ae76-5e49-42a1-91b7-32723abdcf14
-- title:
--   Exact basis-labelled router for the canonical q=6 row-112 block
-- statement:
--   The canonical coarse block of type $112$ in the square of the $q=6$ Coppersmith--Winograd tensor maps onto the four-sum coupled constituent by one explicit family of three linear maps. These maps send the block tensor exactly to the coupled tensor. Moreover, on every named canonical basis coordinate they send the literal CW-square basis pair to the corresponding standard coordinate vector of the coupled constituent. This basis-labelled strengthening of the usual restriction is the coherence needed to compare the enhanced-112 exact-address projector with the prescribed Table-2 word histogram.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Table 2 and the enhanced 112 analysis in Section 6.3; coupled four-sum constituent as in Coppersmith--Winograd (1990), journal pp. 266 and 270. https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_q6_canonical_112_router_data

open MME PiTensorProduct

universe u

set_option autoImplicit false
set_option maxHeartbeats 800000

theorem mme_dwz_q6_canonical_112_basis_labelled_source_router
    (K : Type u) [Field K] :
    ∃ maps : ∀ s : Fin 3,
        (cwSquareCanonicalGrading K 6).classOf s
            (cwSquareBlockType 1 1 2 s) →ₗ[K]
          CoupledSpace K 6 s,
      PiTensorProduct.map maps
          ((cwSquareCanonicalGrading K 6).blockTensor
            (cwSquareBlockType 1 1 2)) =
        coupledTensor K 6 ∧
      ∀ (s : Fin 3) (c : DWZCanonical112Coord 6 s),
        maps s
            ((cwSquareCanonicalGrading K 6).blockProj s
              (cwSquareBlockType 1 1 2 s)
              (cwSquareCanonicalBasis K 6 s
                (dwzCanonical112Pair 6 s c))) =
          dwzCanonical112Vec K 6 s c := by
  sorry

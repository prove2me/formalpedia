-- Prove2me | Theorems.Thm_mme_CW_square_canonical_112_full_basis_router
-- name    : mme_CW_square_canonical_112_full_basis_router
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-06T21:49:16.580941+00:00
-- url     : https://prove2.me/theorems/f8c5dc6a-c5b8-4d27-8a41-490338a52d1f
-- title:
--   General-q canonical112 router with exhaustive all-mode basis coverage
-- statement:
--   For every field and every q, there are explicit mode-wise linear maps from the actual canonical112 CW-square block to the coupled four-sum tensor. Their tensor product maps the actual block tensor exactly to the coupled tensor. For every named coupled coordinate, each map sends its projected canonical CW-square basis vector to that exact standard coupled coordinate vector. Moreover, every canonical coarse-1 X/Y pair and coarse-2 Z pair occurs among these named pairs. Thus the named basis action exhausts the actual source basis, and the literal pair order is retained for complete fine-word filtering. This is not an all-mode profile extraction or a tensor-value estimate.
-- source:
--   General-q port of the accepted explicit q6 router mme_dwz_q6_canonical_112_basis_labelled_source_router (ebc2ae76-5e49-42a1-91b7-32723abdcf14), using its genuinely q-parametric internal construction and public definitions. The added coverage theorem proves the complete canonical pair classification by symbolic coordinate-grade arithmetic. The intended complete-profile consumer is More Asymmetry, https://arxiv.org/abs/2404.16349v2, Definitions3.4-3.6 and Proposition6.3/Theorem6.4. The112 component is a laser-method component, not the zero-coordinate boundary theorem.

import Definitions.Def_mme_dwz_q6_canonical_112_router_data

open MME PiTensorProduct

universe u

set_option autoImplicit false
set_option maxHeartbeats 800000

theorem mme_CW_square_canonical_112_full_basis_router
    (K : Type u) [Field K] (q : ℕ) :
    ∃ maps : ∀ s : Fin 3,
        (cwSquareCanonicalGrading K q).classOf s
            (cwSquareBlockType 1 1 2 s) →ₗ[K]
          CoupledSpace K q s,
      PiTensorProduct.map maps
          ((cwSquareCanonicalGrading K q).blockTensor
            (cwSquareBlockType 1 1 2)) =
        coupledTensor K q ∧
      (∀ (s : Fin 3) (c : DWZCanonical112Coord q s),
        maps s
            ((cwSquareCanonicalGrading K q).blockProj s
              (cwSquareBlockType 1 1 2 s)
              (cwSquareCanonicalBasis K q s
                (dwzCanonical112Pair q s c))) =
          dwzCanonical112Vec K q s c) ∧
      (∀ (s : Fin 3) (p : Fin (q + 2) × Fin (q + 2)),
        cwSquarePairGrade q p = cwSquareBlockType 1 1 2 s →
          ∃ c : DWZCanonical112Coord q s, dwzCanonical112Pair q s c = p) := by sorry

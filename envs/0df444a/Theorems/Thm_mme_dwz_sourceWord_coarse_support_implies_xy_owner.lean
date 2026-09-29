-- Prove2me | Theorems.Thm_mme_dwz_sourceWord_coarse_support_implies_xy_owner
-- name    : mme_dwz_sourceWord_coarse_support_implies_xy_owner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-28T10:12:56.404982+00:00
-- url     : https://prove2.me/theorems/f47751c1-6ca8-47ef-98cd-ce5f2e6e147e
-- title:
--   Source-word coarse support implies X/Y-owner isolation
-- statement:
--   Canonical square-CW support, transported through the source-word reindexing, turns the arithmetic first-hash X/Y-owner isolation condition into the exact nonzero coarse-block isolation premise used by the tensor-family assembly.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_source_aligned_broken_obj
import Definitions.Def_mme_dwz_global_common_state_broken_copy
import Theorems.Thm_mme_CW_square_canonical_support_and_scalar_blocks

open MME

universe u

set_option autoImplicit false

open MME.DWZSourceAligned
open MME.DWZGlobalCorrelated

theorem mme_dwz_sourceWord_coarse_support_implies_xy_owner
    {K : Type u} [Field K] {N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (hXYOwner : ∀ js : Fin 3 → Fin n,
      (∀ t : Fin (N + 1),
        (MME.DWZSquare.shapeX (edge (js 0) t)).val +
          (MME.DWZSquare.shapeY (edge (js 1) t)).val +
          (MME.DWZSquare.shapeZ (edge (js 2) t)).val = 4) →
      js 0 = js 1) :
    ∀ js : Fin 3 → Fin n,
      (∀ r : Fin L,
        (cwSquareCanonicalGrading K 6).blockTensor
          (fun i ↦ coarseAddress
            (sourceWord reindex edge (js i)) i r) ≠ 0) →
      js 0 = js 1 := by
  sorry

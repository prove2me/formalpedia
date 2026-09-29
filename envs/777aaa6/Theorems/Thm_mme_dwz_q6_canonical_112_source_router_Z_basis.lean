-- Prove2me | Theorems.Thm_mme_dwz_q6_canonical_112_source_router_Z_basis
-- name    : mme_dwz_q6_canonical_112_source_router_Z_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T07:39:19.332019+00:00
-- url     : https://prove2.me/theorems/d4a5a50a-20ee-498e-985d-e1403fe48992
-- title:
--   Canonical q=6 row-112 source router with exact Z-basis action
-- statement:
--   There is one family of three linear maps from the literal canonical q=6 row-112 component block to the coupled four-sum constituent which sends the component tensor exactly to the coupled tensor. On every named Z-basis vector, the same third-mode map sends the canonical coarse-grade-two pair to its exactly decoded standard coupled basis coordinate. This supplies the basis-level coherence required by the enhanced-112 shared-Z projector, beyond a quotient-level tensor restriction.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Table 2 and enhanced 112 analysis in Section 6.3; https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_dwz_q6_canonical_112_basis_labelled_source_router
import Theorems.Thm_mme_dwz_q6_112_Z_decoder_pair_and_leftGrade
import Theorems.Thm_mme_dwz_q6_canonicalComponent112_Z_basis_eq_blockProj

open MME PiTensorProduct Module
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option maxHeartbeats 400000

theorem mme_dwz_q6_canonical_112_source_router_Z_basis
    (K : Type u) [Field K] :
    ∃ maps : ∀ s : Fin 3,
        (canonicalComponentBlock K 12).V s →ₗ[K]
          (coupledObj K 6).V s,
      PiTensorProduct.map maps (canonicalComponentBlock K 12).t =
          (coupledObj K 6).t ∧
      ∀ p : LiftedCoarsePair.{u} 6 2,
        maps 2 (canonicalComponentZBasis K 12 p) =
          dwzQ6CoupledBasis K 2 (dwzQ6Canonical112ZCoord p) := by
  sorry

-- Prove2me | Theorems.Thm_mme_dwz_q6_rect103_exact_z_basis_router
-- name    : mme_dwz_q6_rect103_exact_z_basis_router
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T07:39:01.352151+00:00
-- url     : https://prove2.me/theorems/bce25e83-2ae9-406d-b550-dd3562eb6cac
-- title:
--   Exact canonical Z-basis router for the q=6 (1,0,3) constituent
-- statement:
--   For the canonical five-grading at $q=6$, the $(1,0,3)$ constituent restricts exactly to the rotated rectangular tensor $\langle 12,1,1\rangle$. Its twelve coarse-grade-$3$ third-mode basis vectors are routed bijectively to the literal standard third-mode channels in the rotated orientation.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, J. Symbolic Computation 9 (1990), constituent (1,0,3) on pp. 265--266; basis-labelled q=6 specialization for Table-2 extraction.

import Definitions.Def_mme_dwz_component_word_projection

open MME PiTensorProduct Module
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem mme_dwz_q6_rect103_exact_z_basis_router
    (K : Type u) [Field K] :
    ∃ maps : ∀ s : Fin 3,
        (cwSquareCanonicalGrading K 6).classOf s
            (cwSquareBlockType 1 0 3 s) →ₗ[K]
          (MMObj K 12 1 1).V s,
      PiTensorProduct.map maps
          ((cwSquareCanonicalGrading K 6).blockTensor
            (cwSquareBlockType 1 0 3)) =
        MMTensor K 12 1 1 ∧
      ∃ coord : LiftedCoarsePair.{u} 6 3 ↪ Fin 12,
        ∀ p,
          maps 2
              (((coarseClassBasis (K := K) 6 2 3).reindex
                Equiv.ulift.symm) p) =
            (Pi.single ((0 : Fin 1), coord p) 1 : Fin 1 × Fin 12 → K) := by
  sorry

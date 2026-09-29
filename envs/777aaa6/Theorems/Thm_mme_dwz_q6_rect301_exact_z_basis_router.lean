-- Prove2me | Theorems.Thm_mme_dwz_q6_rect301_exact_z_basis_router
-- name    : mme_dwz_q6_rect301_exact_z_basis_router
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T07:39:10.602637+00:00
-- url     : https://prove2.me/theorems/ec045904-e434-4987-ab2a-63d72027d05e
-- title:
--   Exact canonical Z-basis router for the q=6 (3,0,1) constituent
-- statement:
--   For the canonical five-grading at $q=6$, the $(3,0,1)$ constituent restricts exactly to $\langle 12,1,1\rangle$, and the twelve canonical coarse-grade-$1$ third-mode basis vectors are routed bijectively to the literal standard channels. This is the grade-reversed rotated companion of the $(1,0,3)$ router.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, J. Symbolic Computation 9 (1990), constituent (3,0,1) on pp. 265--266; basis-labelled q=6 specialization for Table-2 extraction.

import Definitions.Def_mme_dwz_component_word_projection

open MME PiTensorProduct Module
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem mme_dwz_q6_rect301_exact_z_basis_router
    (K : Type u) [Field K] :
    ∃ maps : ∀ s : Fin 3,
        (cwSquareCanonicalGrading K 6).classOf s
            (cwSquareBlockType 3 0 1 s) →ₗ[K]
          (MMObj K 12 1 1).V s,
      PiTensorProduct.map maps
          ((cwSquareCanonicalGrading K 6).blockTensor
            (cwSquareBlockType 3 0 1)) =
        MMTensor K 12 1 1 ∧
      ∃ coord : LiftedCoarsePair.{u} 6 1 ↪ Fin 12,
        ∀ p,
          maps 2
              (((coarseClassBasis (K := K) 6 2 1).reindex
                Equiv.ulift.symm) p) =
            (Pi.single ((0 : Fin 1), coord p) 1 : Fin 1 × Fin 12 → K) := by
  sorry

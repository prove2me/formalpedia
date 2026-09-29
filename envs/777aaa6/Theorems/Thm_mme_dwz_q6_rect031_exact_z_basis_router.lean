-- Prove2me | Theorems.Thm_mme_dwz_q6_rect031_exact_z_basis_router
-- name    : mme_dwz_q6_rect031_exact_z_basis_router
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T07:38:52.366286+00:00
-- url     : https://prove2.me/theorems/9132e46d-5e92-4584-ac93-37c5a57c34af
-- title:
--   Exact canonical Z-basis router for the q=6 (0,3,1) constituent
-- statement:
--   For the canonical five-grading at $q=6$, the $(0,3,1)$ constituent restricts exactly to $\langle 1,1,12\rangle$, with the twelve canonical third-mode basis vectors of coarse grade $1$ routed bijectively to the literal standard channels. This is the grade-reversed companion of the $(0,1,3)$ router.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, J. Symbolic Computation 9 (1990), constituent (0,3,1) on pp. 265--266; basis-labelled q=6 specialization for Table-2 extraction.

import Definitions.Def_mme_dwz_component_word_projection

open MME PiTensorProduct Module
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem mme_dwz_q6_rect031_exact_z_basis_router
    (K : Type u) [Field K] :
    ∃ maps : ∀ s : Fin 3,
        (cwSquareCanonicalGrading K 6).classOf s
            (cwSquareBlockType 0 3 1 s) →ₗ[K]
          (MMObj K 1 1 12).V s,
      PiTensorProduct.map maps
          ((cwSquareCanonicalGrading K 6).blockTensor
            (cwSquareBlockType 0 3 1)) =
        MMTensor K 1 1 12 ∧
      ∃ coord : LiftedCoarsePair.{u} 6 1 ↪ Fin 12,
        ∀ p,
          maps 2
              (((coarseClassBasis (K := K) 6 2 1).reindex
                Equiv.ulift.symm) p) =
            (Pi.single (coord p, (0 : Fin 1)) 1 : Fin 12 × Fin 1 → K) := by
  sorry

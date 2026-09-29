-- Prove2me | Theorems.Thm_mme_dwz_q6_rect013_exact_z_basis_router
-- name    : mme_dwz_q6_rect013_exact_z_basis_router
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T07:38:44.87062+00:00
-- url     : https://prove2.me/theorems/4b036016-2b8b-4dd6-bb17-3f9401efa0db
-- title:
--   Exact canonical Z-basis router for the q=6 (0,1,3) constituent
-- statement:
--   For the canonical five-grading of the square of the Coppersmith--Winograd tensor at $q=6$, the $(0,1,3)$ constituent admits an exact restriction to the rectangular matrix-multiplication tensor $\langle 1,1,12\rangle$. Moreover, its twelve canonical third-mode basis vectors of coarse grade $3$ are carried bijectively to the twelve literal standard third-mode channels. This basis-labelled form is the input needed to retain an arbitrary equal-multiplicity subset of channels in tensor powers.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, J. Symbolic Computation 9 (1990), constituent (0,1,3) in the tensor-square construction on pp. 265--266; basis-labelled q=6 specialization for the Duan--Wu--Zhou Table-2 extraction.

import Definitions.Def_mme_dwz_component_word_projection

open MME PiTensorProduct Module
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem mme_dwz_q6_rect013_exact_z_basis_router
    (K : Type u) [Field K] :
    ∃ maps : ∀ s : Fin 3,
        (cwSquareCanonicalGrading K 6).classOf s
            (cwSquareBlockType 0 1 3 s) →ₗ[K]
          (MMObj K 1 1 12).V s,
      PiTensorProduct.map maps
          ((cwSquareCanonicalGrading K 6).blockTensor
            (cwSquareBlockType 0 1 3)) =
        MMTensor K 1 1 12 ∧
      ∃ coord : LiftedCoarsePair.{u} 6 3 ↪ Fin 12,
        ∀ p,
          maps 2
              (((coarseClassBasis (K := K) 6 2 3).reindex
                Equiv.ulift.symm) p) =
            (Pi.single (coord p, (0 : Fin 1)) 1 : Fin 12 × Fin 1 → K) := by
  sorry

-- Prove2me | Theorems.Thm_mme_dwz_table2_balanced_rows_exact_allowed_dimension
-- name    : mme_dwz_table2_balanced_rows_exact_allowed_dimension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T08:43:14.019789+00:00
-- url     : https://prove2.me/theorems/79be2b60-ec4e-4123-847e-7586c45af1aa
-- title:
--   Exact available-word dimensions for the four balanced Table-2 rows
-- statement:
--   Fix a field $K$. Assume exact basis-labelled one-letter restrictions for the four rectangular Coppersmith--Winograd blocks $013$, $031$, $103$, and $301$, including injective routing of every canonical coarse $Z$-basis vector to its named coordinate in $\langle1,1,12\rangle$ or $\langle12,1,1\rangle$. For every Table-2 scale $m$ and every row $s\in\{3,4,5,7\}$, let $D_s(m)$ be the number of canonical $Z$-words that obey the row's prescribed equal-multiplicity availability condition. Then the literal projected component power restricts to one rectangular matrix-multiplication tensor $\langle a,b,c\rangle$ with
--
--   $$
--   abc=D_s(m).
--   $$
--
--   Thus the nontrivial matrix dimension is exactly the number of retained canonical words, rather than merely an abstract space of the same dimension. This isolates the finite algebraic realization of the four balanced rows from the subsequent multinomial lower bound and subexponential-loss analysis.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6.3 and Table 2, balanced rectangular rows 013, 031, 103, and 301.

import Definitions.Def_mme_dwz_component_word_projection
import Theorems.Thm_mme_power_basisZAllowedSubtensor_restrict_MM_oneOne_of_exact_router
import Theorems.Thm_mme_power_basisZAllowedSubtensor_restrict_MM_first_of_exact_router

open MME PiTensorProduct Module
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem mme_dwz_table2_balanced_rows_exact_allowed_dimension
    {K : Type u} [Field K]
    (h013 :
      ∃ maps : ∀ s : Fin 3,
          (cwSquareCanonicalGrading K 6).classOf s
              (cwSquareBlockType 0 1 3 s) →ₗ[K]
            (MMObj K 1 1 12).V s,
        PiTensorProduct.map maps
            ((cwSquareCanonicalGrading K 6).blockTensor
              (cwSquareBlockType 0 1 3)) = MMTensor K 1 1 12 ∧
        ∃ coord : LiftedCoarsePair.{u} 6 3 ↪ Fin 12,
          ∀ p, maps 2
              (((coarseClassBasis (K := K) 6 2 3).reindex
                Equiv.ulift.symm) p) =
            (Pi.single (coord p, (0 : Fin 1)) 1 : Fin 12 × Fin 1 → K))
    (h031 :
      ∃ maps : ∀ s : Fin 3,
          (cwSquareCanonicalGrading K 6).classOf s
              (cwSquareBlockType 0 3 1 s) →ₗ[K]
            (MMObj K 1 1 12).V s,
        PiTensorProduct.map maps
            ((cwSquareCanonicalGrading K 6).blockTensor
              (cwSquareBlockType 0 3 1)) = MMTensor K 1 1 12 ∧
        ∃ coord : LiftedCoarsePair.{u} 6 1 ↪ Fin 12,
          ∀ p, maps 2
              (((coarseClassBasis (K := K) 6 2 1).reindex
                Equiv.ulift.symm) p) =
            (Pi.single (coord p, (0 : Fin 1)) 1 : Fin 12 × Fin 1 → K))
    (h103 :
      ∃ maps : ∀ s : Fin 3,
          (cwSquareCanonicalGrading K 6).classOf s
              (cwSquareBlockType 1 0 3 s) →ₗ[K]
            (MMObj K 12 1 1).V s,
        PiTensorProduct.map maps
            ((cwSquareCanonicalGrading K 6).blockTensor
              (cwSquareBlockType 1 0 3)) = MMTensor K 12 1 1 ∧
        ∃ coord : LiftedCoarsePair.{u} 6 3 ↪ Fin 12,
          ∀ p, maps 2
              (((coarseClassBasis (K := K) 6 2 3).reindex
                Equiv.ulift.symm) p) =
            (Pi.single ((0 : Fin 1), coord p) 1 : Fin 1 × Fin 12 → K))
    (h301 :
      ∃ maps : ∀ s : Fin 3,
          (cwSquareCanonicalGrading K 6).classOf s
              (cwSquareBlockType 3 0 1 s) →ₗ[K]
            (MMObj K 12 1 1).V s,
        PiTensorProduct.map maps
            ((cwSquareCanonicalGrading K 6).blockTensor
              (cwSquareBlockType 3 0 1)) = MMTensor K 12 1 1 ∧
        ∃ coord : LiftedCoarsePair.{u} 6 1 ↪ Fin 12,
          ∀ p, maps 2
              (((coarseClassBasis (K := K) 6 2 1).reindex
                Equiv.ulift.symm) p) =
            (Pi.single ((0 : Fin 1), coord p) 1 : Fin 1 × Fin 12 → K)) :
    ∀ (m : ℕ) (s : Fin 15), (s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 7) →
      let D := Nat.card
        {w : PowIndex (LiftedCoarsePair.{u} 6 (MME.DWZSquare.shapeZ s))
            (MME.DWZTable2Counts.component s * m) //
          componentWordAllowed s m w}
      ∃ a b c : ℕ,
        TensorObj.Restrict (MMObj K a b c) (restrictedComponentPower K s m) ∧
        a * b * c = D := by
  sorry

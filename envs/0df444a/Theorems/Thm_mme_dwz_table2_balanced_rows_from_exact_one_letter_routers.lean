-- Prove2me | Theorems.Thm_mme_dwz_table2_balanced_rows_from_exact_one_letter_routers
-- name    : mme_dwz_table2_balanced_rows_from_exact_one_letter_routers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T08:00:50.611321+00:00
-- url     : https://prove2.me/theorems/5f07203c-0e13-4b01-8adb-ce59142dda8a
-- title:
--   Balanced rectangular Table-2 rows from exact one-letter routers
-- statement:
--   Assume exact, basis-labelled one-letter restrictions for the four q=6 rectangular CW-square constituents (0,1,3), (0,3,1), (1,0,3), and (3,0,1). Then, for every tau at least 2/3 and all sufficiently large integral scales, each corresponding Table-2 component power retains a matrix-multiplication tensor after the literal equal-multiplicity Z-word projection. Its six-copy weighted volume loses at most an explicit factor exp(-C sqrt(10^16 m+1)). This theorem isolates exactly the remaining power-lifting, available-word enumeration, and polynomial-to-square-root-loss analysis from the already verified one-letter algebra.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Section 6.3 and Table 2, arXiv:2210.10173v5; balanced rectangular constituents and equal-multiplicity available-Z extraction.

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Definitions.Def_mme_dwz_square_data
import Definitions.Def_mme_dwz_table2_integer_counts
import Definitions.Def_mme_dwz_component_word_projection

open MME Filter
open MME.DWZSquare MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem mme_dwz_table2_balanced_rows_from_exact_one_letter_routers
    {K : Type u} [Field K]
    (h013 :
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
              (Pi.single (coord p, (0 : Fin 1)) 1 :
                Fin 12 × Fin 1 → K))
    (h031 :
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
              (Pi.single (coord p, (0 : Fin 1)) 1 :
                Fin 12 × Fin 1 → K))
    (h103 :
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
              (Pi.single ((0 : Fin 1), coord p) 1 :
                Fin 1 × Fin 12 → K))
    (h301 :
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
              (Pi.single ((0 : Fin 1), coord p) 1 :
                Fin 1 × Fin 12 → K))
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        ∀ s : Fin 15, (s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 7) →
          ∃ a b c : ℕ,
            TensorObj.Restrict (MMObj K a b c)
              (restrictedComponentPower K s m) ∧
            (((componentBase tau s) ^
                (MME.DWZTable2Counts.component s * m)) ^ (6 : ℕ)) *
                Real.exp (-C * Real.sqrt
                  (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ≤
              (((((a * b * c) ^ 2) * ((a * b * c) ^ 2) *
                    ((a * b * c) ^ 2) : ℕ) : ℝ) ^ tau) := by
  sorry

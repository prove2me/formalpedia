-- Prove2me | Theorems.Thm_mme_dwz_table2_112_row_six_symmetric_finite_extraction_sqrt_loss
-- name    : mme_dwz_table2_112_row_six_symmetric_finite_extraction_sqrt_loss
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T18:47:26.200264+00:00
-- url     : https://prove2.me/theorems/9dad48ad-dd7b-4182-8859-1fbf9de44956
-- title:
--   Table 2 finite extraction: enhanced 112 row
-- statement:
--   For $\tau\ge2/3$, the enhanced restricted $112$ component power at Table-2 index $12$ admits a finite six-symmetric matrix-multiplication extraction at the printed split-$b$ component base, with at most a square-root-exponential loss. This is the finite router-and-hashing form of the paper's enhanced $112$ value analysis.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, the enhanced 112 analysis in Sections 4 and 6.3 and Table 2, arXiv:2210.10173v5.

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Definitions.Def_mme_dwz_square_data
import Definitions.Def_mme_dwz_table2_integer_counts
import Definitions.Def_mme_dwz_component_word_projection
import Definitions.Def_mme_six_symmetrized_tau_value

open MME BigOperators Filter
open MME.DWZSquare MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem mme_dwz_table2_112_row_six_symmetric_finite_extraction_sqrt_loss
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        ∃ (q : ℕ) (A B Cdim : Fin q → ℕ),
          TensorObj.Restrict
            (TensorObj.bigAdd (fun j => MMObj K (A j) (B j) (Cdim j)))
            (sixSymmetrization
              (restrictedComponentPower K (12 : Fin 15) m)) ∧
          (((componentBase tau (12 : Fin 15)) ^
              (MME.DWZTable2Counts.component (12 : Fin 15) * m)) ^ (6 : ℕ)) *
              Real.exp (-C * Real.sqrt
                (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ≤
            ∑ j, (((A j * B j * Cdim j : ℕ) : ℝ) ^ tau) := by
  sorry

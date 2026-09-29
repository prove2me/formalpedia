-- Prove2me | Theorems.Thm_mme_dwz_table2_121_211_rows_six_symmetric_finite_extraction_sqrt_loss
-- name    : mme_dwz_table2_121_211_rows_six_symmetric_finite_extraction_sqrt_loss
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T18:47:41.068964+00:00
-- url     : https://prove2.me/theorems/867af121-7059-46bf-8408-f6f266f35da6
-- title:
--   Table 2 finite extraction: cyclic 121 and 211 rows
-- statement:
--   For $\tau\ge2/3$, the two distinct cyclic restricted component powers $121$ and $211$ at Table-2 indices $13$ and $14$ admit uniform finite six-symmetric matrix-multiplication extractions at their common printed component base, with at most a square-root-exponential loss. The two cyclic routers are retained as separate tensor constructions.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, the cyclic 121/211 analysis in Section 6.3 and Table 2, arXiv:2210.10173v5.

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

theorem mme_dwz_table2_121_211_rows_six_symmetric_finite_extraction_sqrt_loss
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        ∀ s : Fin 15, (s = 13 ∨ s = 14) →
          ∃ (q : ℕ) (A B Cdim : Fin q → ℕ),
            TensorObj.Restrict
              (TensorObj.bigAdd (fun j => MMObj K (A j) (B j) (Cdim j)))
              (sixSymmetrization (restrictedComponentPower K s m)) ∧
            (((componentBase tau s) ^
                (MME.DWZTable2Counts.component s * m)) ^ (6 : ℕ)) *
                Real.exp (-C * Real.sqrt
                  (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ≤
              ∑ j, (((A j * B j * Cdim j : ℕ) : ℝ) ^ tau) := by
  sorry

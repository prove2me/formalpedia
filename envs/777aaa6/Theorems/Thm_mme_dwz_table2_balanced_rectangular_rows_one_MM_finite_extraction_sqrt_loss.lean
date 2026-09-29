-- Prove2me | Theorems.Thm_mme_dwz_table2_balanced_rectangular_rows_one_MM_finite_extraction_sqrt_loss
-- name    : mme_dwz_table2_balanced_rectangular_rows_one_MM_finite_extraction_sqrt_loss
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T20:57:24.441483+00:00
-- url     : https://prove2.me/theorems/da563f23-0639-4f86-98ac-9bd24e93647e
-- title:
--   Finite rectangular extraction for the four balanced elementary Table-2 rows
-- statement:
--   Fix a field $K$ and $\tau\ge2/3$. For every sufficiently large scale $m$, each of the four elementary rectangular Table-2 rows $s\in\{3,4,5,7\}$ contains one matrix-multiplication tensor $\langle a,b,c\rangle$ after the prescribed balanced available-$Z$-word projection, and its six-copy weighted volume obeys
--
--   $$
--   B_s(\tau)^{6n_s(m)}e^{-C\sqrt{10^{16}m+1}}\le\bigl((abc)^6\bigr)^\tau.
--   $$
--
--   These are precisely the elementary rows whose coarse $Z$-grade permits two fine grades and whose exact Table-2 split requires equal multiplicities. All forced-profile scalar, rectangular, and central-$220$ rows are handled by a separate exact theorem with zero loss.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Lemma 4.6 and Section 6.3/Table 2, arXiv:2210.10173v5; the balanced rectangular rows 013, 031, 103, and 301.

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Definitions.Def_mme_dwz_square_data
import Definitions.Def_mme_dwz_table2_integer_counts
import Definitions.Def_mme_dwz_component_word_projection

open MME Filter
open MME.DWZSquare MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem mme_dwz_table2_balanced_rectangular_rows_one_MM_finite_extraction_sqrt_loss
    {K : Type u} [Field K]
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

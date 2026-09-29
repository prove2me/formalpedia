-- Prove2me | Theorems.Thm_mme_dwz_table2_elementary_component_rows_one_MM_finite_extraction_sqrt_loss
-- name    : mme_dwz_table2_elementary_component_rows_one_MM_finite_extraction_sqrt_loss
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T20:41:39.448409+00:00
-- url     : https://prove2.me/theorems/7ff8ea41-9a51-4fb6-b3bb-03226071daf7
-- title:
--   Each restricted elementary Table-2 row contains one rate-achieving rectangular product
-- statement:
--   Fix a field $K$ and $\tau\ge2/3$. For every sufficiently large Table-2 scaling parameter $m$, each of the three scalar rows, six rectangular rows, and the central $220$ row contains an actual rectangular matrix-multiplication tensor $\langle a,b,c\rangle$ after the prescribed available-$Z$-word projection. Uniformly over these ten rows, its six-symmetrized weighted volume satisfies
--
--   $$
--   B_s(\tau)^{6n_s(m)}e^{-C\sqrt{10^{16}m+1}}\le((abc)^6)^\tau.
--   $$
--
--   Here $B_s(\tau)$ is the exact Section-6.3 component base and $n_s(m)$ is the exact integral Table-2 multiplicity. This theorem isolates the only row-specific tensor realization and counting step: the passage from this one rectangular product to the full six-symmetric finite extraction is a separate proved tensor-isomorphism adapter.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Lemma 4.6 and Section 6.3/Table 2, arXiv:2210.10173v5. The scalar, rectangular, and central-220 component restrictions are the ten elementary rows used in the Table-2 value computation.

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Definitions.Def_mme_dwz_square_data
import Definitions.Def_mme_dwz_table2_integer_counts
import Definitions.Def_mme_dwz_component_word_projection

open MME Filter
open MME.DWZSquare MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem mme_dwz_table2_elementary_component_rows_one_MM_finite_extraction_sqrt_loss
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        ∀ s : Fin 15, (s.val ≤ 8 ∨ s = 11) →
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

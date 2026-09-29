-- Prove2me | Theorems.Thm_mme_dwz_q6_022_table2_scaled_dimension_six_finite_rate
-- name    : mme_dwz_q6_022_table2_scaled_dimension_six_finite_rate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T06:53:09.630608+00:00
-- url     : https://prove2.me/theorems/c6e17abf-9174-4743-95ab-aa4174c884c5
-- title:
--   Finite-rate dimension bound for the Table-2 022 extraction
-- statement:
--   Let $D_m$ be the exact number of canonical restricted $022$ words at the integral Table-2 scale $t=10366945m$. For every $tau$ with $2 ≤ 3tau$, there is a nonnegative constant $C$ such that, for all sufficiently large $m$,
--
--   $$
--   (B_{022}(tau)^{N_{022}m})^6 exp(-C sqrt(Sm+1)) ≤ (D_m^{tau})^6.
--   $$
--
--   Here $S=10^{16}$ is the common Table-2 scale and $N_{022}$ is its row-$9$ component count. The square-root exponential absorbs the finite polynomial entropy loss while retaining the exact asymptotic component base.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Lemma 4.6 and the 022 restricted splitting used in Table 2.

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Definitions.Def_mme_dwz_square_data
import Definitions.Def_mme_dwz_table2_integer_counts
import Definitions.Def_mme_dwz_table2_component_022_word_data

open Filter Topology
open MME MME.DWZSquare
open MME.DWZTable2Component022

set_option autoImplicit false

theorem mme_dwz_q6_022_table2_scaled_dimension_six_finite_rate
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        let D := Nat.card (Restricted022Word 6
          (table2Power022 (10366945 * m))
          (table2OuterCount022 (10366945 * m))
          (table2MiddleCount022 (10366945 * m)))
        (((componentBase tau (9 : Fin 15)) ^
            (MME.DWZTable2Counts.component 9 * m)) ^ (6 : ℕ)) *
              Real.exp (-C * Real.sqrt
                (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ≤
          (((D : ℕ) : ℝ) ^ tau) ^ (6 : ℕ) := by
  sorry

-- Prove2me | Theorems.Thm_mme_dwz_q6_balanced_allowed_card_six_finite_rate
-- name    : mme_dwz_q6_balanced_allowed_card_six_finite_rate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T09:34:03.5396+00:00
-- url     : https://prove2.me/theorems/19002061-d17e-4f84-a4e3-c26e2cf34f92
-- title:
--   Six-copy finite rate of the balanced q=6 available-word families
-- statement:
--   Fix $\tau\ge 2/3$. For each sufficiently large Table-2 scale $m$ and each balanced rectangular row $s\in\{3,4,5,7\}$, let $D_s(m)$ be the exact number of available canonical $Z$-words. There is a constant $C\ge0$ such that
--
--   $$
--   B_s(\tau)^{6N_s(m)}e^{-C\sqrt{10^{16}m+1}}
--   \le \bigl(D_s(m)^6\bigr)^\tau.
--   $$
--
--   Here $B_s(\tau)$ is the Section-6.3 component base and $N_s(m)$ is the exact row multiplicity. This theorem is purely quantitative: it contains the balanced multinomial count and polynomial-loss absorption, but no tensor restriction hypothesis or construction.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Lemma 4.6 and Section 6.3/Table 2, balanced rectangular rows 013, 031, 103, and 301.

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Definitions.Def_mme_dwz_square_data
import Definitions.Def_mme_dwz_table2_integer_counts
import Definitions.Def_mme_dwz_component_word_projection

open MME Filter
open MME.DWZSquare MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem mme_dwz_q6_balanced_allowed_card_six_finite_rate
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        ∀ s : Fin 15, (s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 7) →
          let D := Nat.card
            {w : PowIndex
                (LiftedCoarsePair.{u} 6 (MME.DWZSquare.shapeZ s))
                (MME.DWZTable2Counts.component s * m) //
              componentWordAllowed s m w}
          (((componentBase tau s) ^
              (MME.DWZTable2Counts.component s * m)) ^ (6 : ℕ)) *
              Real.exp (-C * Real.sqrt
                (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ≤
            (((D ^ 2) * (D ^ 2) * (D ^ 2) : ℕ) : ℝ) ^ tau := by
  sorry

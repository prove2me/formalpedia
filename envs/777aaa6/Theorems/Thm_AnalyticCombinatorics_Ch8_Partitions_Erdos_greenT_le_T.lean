-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_greenT_le_T
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.greenT_le_T
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T11:06:23.778699+00:00
-- url     : https://prove2.me/theorems/ab3ecbd4-3c72-4713-a3bd-625481552e3a
-- title:
--   A finite-horizon Green upper bound
-- statement:
--   Proves the upper bound finite-horizon Green≤T, not the separate square-root LOWER heat/Green estimate.
--
--   The full literal source contract is:
--
--   ```lean
--   lemma greenT_le_T (T : ℕ) (x y : α) : greenT P rnk W T x y ≤ (T : ℝ)
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/GreenLowerWall.lean#L47. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ITERCoupling
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ITERGreenT
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Green potential bounds (renewal route B capstone support)

`greenT` (ITERGreenT) is the finite-horizon expected window occupation under the substochastic
residual kernel `Kres` (row sum `1 − cmass ≤ 1`).  This file banks the elementary upper bound
`greenT ≤ T` (each residual iterate of the window indicator is `≤ 1`).  The matching lower bound
`greenT ≥ c√T` (`greenT_lower_fixed_window`) is the lone analytic wall (see `DOCTRINE-walls.md`).
-/

open Finset

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (P : α → α → ℝ) (rnk : α → ℕ) (W : ℕ)
variable (hPnn : ∀ x y, 0 ≤ P x y) (hPmass : ∀ x, ∑ y, P x y = 1)
include hPnn hPmass

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.greenT_le_T (T : ℕ) (x y : α) : greenT P rnk W T x y ≤ (T : ℝ) := by sorry

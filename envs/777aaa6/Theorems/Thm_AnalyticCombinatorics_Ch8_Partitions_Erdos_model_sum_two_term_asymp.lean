-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_model_sum_two_term_asymp
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.model_sum_two_term_asymp
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T17:47:01.403997+00:00
-- url     : https://prove2.me/theorems/b5016987-2169-430a-89a7-2ea2bd8d91a8
-- title:
--   Model sum two-term asymptotic
-- statement:
--   **Model sum two-term asymptotic**: `|model_sum − (μ̄ + μA/√n)| ≤ K/n` for large n.
--
--     The identity `model_sum = c₁·M₁ + c₂·M₂ + c₃·M₃ + c₄·M₄` (Lemma `model_sum_eq_moments`)
--     is combined with the banked moment asymptotics.
--
--   The full literal source contract is:
--
--   ```lean
--   theorem model_sum_two_term_asymp :
--       ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
--         |(∑' m : ℕ, if m = 0 then (0:ℝ) else modelSummand n m * rhoDropModel n m)
--           - (3 / massLam + (3 / (2 * massLam ^ 2)) / Real.sqrt (n : ℝ))|
--         ≤ K / (n : ℝ)
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/MuNumExpansion.lean#L178. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MuNumModel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateMoments
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateApprox2
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# MuNum two-term expansion

`|muNum n − (μ̄ + μA/√n)| ≤ K/n` for large `n`, where
`μ̄ = 3/massLam` and `μA = 3/(2·massLam²)`.
-/

set_option maxHeartbeats 4000000

open Filter Finset
open scoped Topology BigOperators

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos

/-! ### Algebraic expansion of the model product -/

/-! ### Model sum expressed via sigma moments (infinite-sum identity) -/

/-! ### Small lemmas -/

/-! ### Two-term asymptotic from the moment asymptotics -/

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.model_sum_two_term_asymp :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      |(∑' m : ℕ, if m = 0 then (0:ℝ) else modelSummand n m * rhoDropModel n m)
        - (3 / massLam + (3 / (2 * massLam ^ 2)) / Real.sqrt (n : ℝ))|
      ≤ K / (n : ℝ) := by sorry

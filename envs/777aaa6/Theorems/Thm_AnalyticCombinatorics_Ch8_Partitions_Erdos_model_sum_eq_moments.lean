-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_model_sum_eq_moments
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.model_sum_eq_moments
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T17:21:14.103678+00:00
-- url     : https://prove2.me/theorems/3b052864-a921-4a25-a049-a38cb829c444
-- title:
--   Tsum of modelSummand·rhoDropModel = c₁·M₁ + c₂·M₂ + c₃·M₃ + c₄·M₄
-- statement:
--   `tsum` of `modelSummand·rhoDropModel = c₁·M₁ + c₂·M₂ + c₃·M₃ + c₄·M₄`.
--
--   The full literal source contract is:
--
--   ```lean
--   lemma model_sum_eq_moments (n : ℕ) (hn1 : 1 ≤ n) :
--       (∑' m : ℕ, if m = 0 then (0:ℝ) else modelSummand n m * rhoDropModel n m)
--       = (3 / (2 * (n:ℝ) * Real.sqrt (n:ℝ))) * sigmaMoment 1 (massLam / Real.sqrt (n:ℝ))
--       + (15 / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ))) * sigmaMoment 2 (massLam / Real.sqrt (n:ℝ))
--       + ((3 / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ) ^ 3)
--          - 3 * C / (16 * (n:ℝ) ^ 3)) * sigmaMoment 3 (massLam / Real.sqrt (n:ℝ))
--       + ((-3 * C / (64 * (n:ℝ) ^ 4)) * sigmaMoment 4 (massLam / Real.sqrt (n:ℝ))))
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/MuNumExpansion.lean#L74. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

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

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.model_sum_eq_moments (n : ℕ) (hn1 : 1 ≤ n) :
    (∑' m : ℕ, if m = 0 then (0:ℝ) else modelSummand n m * rhoDropModel n m)
    = (3 / (2 * (n:ℝ) * Real.sqrt (n:ℝ))) * sigmaMoment 1 (massLam / Real.sqrt (n:ℝ))
    + (15 / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ))) * sigmaMoment 2 (massLam / Real.sqrt (n:ℝ))
    + ((3 / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ) ^ 3)
       - 3 * C / (16 * (n:ℝ) ^ 3)) * sigmaMoment 3 (massLam / Real.sqrt (n:ℝ))
    + ((-3 * C / (64 * (n:ℝ) ^ 4)) * sigmaMoment 4 (massLam / Real.sqrt (n:ℝ)))) := by sorry

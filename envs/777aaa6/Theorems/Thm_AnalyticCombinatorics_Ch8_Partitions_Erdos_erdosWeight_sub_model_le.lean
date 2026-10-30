-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_erdosWeight_sub_model_le
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.erdosWeight_sub_model_le
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T16:21:20.656003+00:00
-- url     : https://prove2.me/theorems/d3017bad-ab4f-4ee7-97e4-867c9dc92a35
-- title:
--   Per-term error
-- statement:
--   **Per-term error** (§5 brick 3): on the main range (`2m≤n`, `4Cm²≤√n³`), the per-`m` error
--   `|erdosWeight n m − modelSummand n m|` is `σ(m)·#97RHS` — i.e. the divisor-weighted form of
--   `erdosWeight_coef_second_order` (#97).  Both `erdosWeight` and `modelSummand` factor as `σ(m)·(·)`.
--
--   The full literal source contract is:
--
--   ```lean
--   theorem erdosWeight_sub_model_le {n m : ℕ} (hn : 1 ≤ n) (hm1 : 1 ≤ m)
--       (h2m : 2 * m ≤ n) (hsmall : 4 * C * (m:ℝ) ^ 2 ≤ Real.sqrt (n:ℝ) ^ 3) :
--       |erdosWeight n m - modelSummand n m|
--         ≤ Sigma.sigmaR m * ((3 * C ^ 2 + 5 * C + 2) *
--             Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)) *
--             ((m:ℝ) ^ 2 / (n:ℝ) ^ 3 + (m:ℝ) ^ 3 / ((n:ℝ) ^ 3 * Real.sqrt (n:ℝ))
--               + (m:ℝ) ^ 4 / (n:ℝ) ^ 4))
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/MassRateApprox2.lean#L175. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateMoments
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateApprox2
import Mathlib

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos.Close end AnalyticCombinatorics.Ch8.Partitions.Erdos.Close

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Mass-rate campaign: §5 the second-order divisor calc

`kernelMass n = ∑_{m=1}^{n-1} σ(m)/(n−m)·exp(−C(√n−√(n−m)))` versus
`kernelMassApprox2 n = (1/n)M₀(t)+(1/n²)M₁(t)−(C/(8n²√n))M₂(t)` at `t=λ/√n`.

Brick 1 here: `kernelMassApprox2 n = ∑' m, modelSummand n m`, where
`modelSummand n m = σ(m)·e^{−tm}·(1/n + m/n² − Cm²/(8n²√n))` — i.e. the moment package collapses
to a single divisor-weighted Lambert sum.  This is the object the per-term estimate
`erdosWeight_coef_second_order` (#97), multiplied by `σ(m)≥0`, is compared against.  Opus-authored.
-/

set_option maxHeartbeats 1000000

open Filter
open scoped Topology BigOperators

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos

open AnalyticCombinatorics.Ch8.Partitions.Erdos.Close

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.erdosWeight_sub_model_le {n m : ℕ} (hn : 1 ≤ n) (hm1 : 1 ≤ m)
    (h2m : 2 * m ≤ n) (hsmall : 4 * C * (m:ℝ) ^ 2 ≤ Real.sqrt (n:ℝ) ^ 3) :
    |erdosWeight n m - modelSummand n m|
      ≤ Sigma.sigmaR m * ((3 * C ^ 2 + 5 * C + 2) *
          Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)) *
          ((m:ℝ) ^ 2 / (n:ℝ) ^ 3 + (m:ℝ) ^ 3 / ((n:ℝ) ^ 3 * Real.sqrt (n:ℝ))
            + (m:ℝ) ^ 4 / (n:ℝ) ^ 4)) := by sorry

-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_kernelMass_sub_approx2
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.kernelMass_sub_approx2
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T17:47:17.706477+00:00
-- url     : https://prove2.me/theorems/cfc6e601-2704-4ca8-af6e-2a2e1da7b326
-- title:
--   Second-order divisor calc
-- statement:
--   **Second-order divisor calc** (§5 assembly): `|kernelMass n − kernelMassApprox2 n| ≤ K/n`. The
--   main-range error (#brick 4), the far-`erdosWeight` tail (#brick 6) and the `modelSummand` tail
--   (#brick 5) each contribute `O(1/n)`.
--
--   The full literal source contract is:
--
--   ```lean
--   theorem kernelMass_sub_approx2 :
--       ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in Filter.atTop,
--         |kernelMass n - kernelMassApprox2 n| ≤ K / (n:ℝ)
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/MassRateApprox2.lean#L10. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_KernelBarriers
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateMoments
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateAssembly
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

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.kernelMass_sub_approx2 :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in Filter.atTop,
      |kernelMass n - kernelMassApprox2 n| ≤ K / (n:ℝ) := by sorry

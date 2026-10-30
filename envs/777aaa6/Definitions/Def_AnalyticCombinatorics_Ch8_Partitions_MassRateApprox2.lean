-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateApprox2
-- name    : AnalyticCombinatorics_Ch8_Partitions_MassRateApprox2
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T16:15:23.132556+00:00
-- url     : https://prove2.me/theorems/e395bb09-b3fb-43e0-a5c8-6d0a5d68297f
-- title:
--   Mass Rate Approx2 mathematical objects
-- statement:
--   The model summand combines an exponentially damped divisor weight with reciprocal powers of n and a quadratic correction; a private tail function provides truncation control.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/MassRateApprox2.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateMoments
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
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

noncomputable section

open Filter
open scoped Topology BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

open AnalyticCombinatorics.Ch8.Partitions.Erdos.Close

/-- The model (leading-order) summand of the kernel mass at `m`: the divisor-weighted Lambert term
whose tsum over `m` is `kernelMassApprox2 n`. -/
noncomputable def modelSummand (n m : ℕ) : ℝ :=
  if m = 0 then 0
  else Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ))
    * (1 / (n:ℝ) + (m:ℝ) / (n:ℝ) ^ 2 - C * (m:ℝ) ^ 2 / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ)))

end AnalyticCombinatorics.Ch8.Partitions.Erdos



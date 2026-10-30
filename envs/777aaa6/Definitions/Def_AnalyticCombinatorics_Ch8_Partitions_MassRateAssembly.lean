-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateAssembly
-- name    : AnalyticCombinatorics_Ch8_Partitions_MassRateAssembly
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T17:45:43.702995+00:00
-- url     : https://prove2.me/theorems/35920a27-f156-4b41-8871-58ab84cfb946
-- title:
--   Mass Rate Assembly mathematical objects
-- statement:
--   kernelMassApprox2 is the explicit second approximation to the partition recurrence kernel mass.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/MassRateAssembly.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateMoments
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Mass-rate campaign: §6 the √n-cancellation in the second-order approximation

`kernelMassApprox2 n = (1/n)·M₀(t) + (1/n²)·M₁(t) − (C/(8n²√n))·M₂(t)` at `t = lam/√n` satisfies
`|kernelMassApprox2 n − 1| ≤ K/n` eventually: the three weak asymptotics give a leading `1`, the
`1/√n` terms cancel exactly (`mass_rate_sqrt_coeff_cancel`, `massLam_sq` i.e. `lam²=π²/6`), and all
remainders are `O(1/n)`.  Opus-authored.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Filter
open scoped Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- The second-order approximation to the kernel mass (R8 §5). -/
noncomputable def kernelMassApprox2 (n : ℕ) : ℝ :=
  let t := massLam / Real.sqrt (n : ℝ)
  (1 / (n : ℝ)) * sigmaMoment 0 t
  + (1 / (n : ℝ) ^ 2) * sigmaMoment 1 t
  - (C / (8 * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ))) * sigmaMoment 2 t

end AnalyticCombinatorics.Ch8.Partitions.Erdos



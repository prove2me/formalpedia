-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MuTilde_x1
-- name    : AnalyticCombinatorics_Ch8_Partitions_MuTilde_x1
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T19:07:43.283639+00:00
-- url     : https://prove2.me/theorems/7d7282b5-4e8e-4deb-9d95-a1f541e20cef
-- title:
--   Mu Tilde (continued)
-- statement:
--   Further source definitions of this module, published separately from its first definition file (which this one builds on).
--
--   ```lean
--   noncomputable def muTilde (n : ℕ) : ℝ := muNum n / kernelMass n
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/MuTilde.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_KernelBarriers
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MuTilde
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# The smooth-rank conditional drift `μ̃` and its chain-drift identity

For the killed Erdős predecessor chain (`Pker n k = erdosWeight n (n−k)/kernelMass n`), the
martingale coordinate is the smooth rank `ρ(n) = 3√n`.  The one-step conditional decrement is

  `μ̃(n) = E_{k∼Pker(n,·)}[ρ(n) − ρ(k)] = 3 ∑_k Pker(n,k)(√n − √k)`.

This file defines `μ̃` via the predecessor (decrement) sum and records the identity tying it to the
chain drift through the reflection `k ↦ n−k` (`Pker_sum_mul`).  The two-term expansion
`μ̃(n) = μ̄ + μA/√n + O(1/n)` (the input to `two_term_local_lip`) is built in subsequent files from
the banked moment asymptotics (`sigmaMoment_one_two_term`, `sigmaMoment_two_asymp_weak`,
`sigmaMoment_le_power_sharp 3`) and the kernel-mass rate (`kernelMass → 1`).  Opus-authored.
-/

noncomputable section

open Filter Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- The smooth-rank conditional drift `μ̃(n) = muNum n / kernelMass n`. -/
noncomputable def muTilde (n : ℕ) : ℝ := muNum n / kernelMass n

end AnalyticCombinatorics.Ch8.Partitions.Erdos



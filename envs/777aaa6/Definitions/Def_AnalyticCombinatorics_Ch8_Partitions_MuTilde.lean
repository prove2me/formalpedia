-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MuTilde
-- name    : AnalyticCombinatorics_Ch8_Partitions_MuTilde
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T16:13:04.343998+00:00
-- url     : https://prove2.me/theorems/075dbc19-c45f-4754-8a7c-3b4114b53b65
-- title:
--   Mu Tilde
-- statement:
--   The source mathematical objects and operations are specified by the following definitions.
--
--   ```lean
--   noncomputable def rhoDrop (n m : ℕ) : ℝ :=
--     3 * (Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ))
--   ```
--
--   ```lean
--   noncomputable def muNum (n : ℕ) : ℝ :=
--     ∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n m * rhoDrop n m
--   ```
--
--   ```lean
--   noncomputable def muTilde (n : ℕ) : ℝ := muNum n / kernelMass n
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/MuTilde.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
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

/-- The smooth-rank drop `3(√n − √(n−m))` from state `n` to predecessor value `n−m`
(decrement `m`). -/
noncomputable def rhoDrop (n m : ℕ) : ℝ :=
  3 * (Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ))

/-- The (unnormalized) drift numerator `∑_{m=1}^{n-1} erdosWeight n m · ρ-drop`. -/
noncomputable def muNum (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n m * rhoDrop n m

end AnalyticCombinatorics.Ch8.Partitions.Erdos



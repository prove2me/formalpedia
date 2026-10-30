-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_muTilde_expansion_of_muNum
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.muTilde_expansion_of_muNum
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T19:09:02.443846+00:00
-- url     : https://prove2.me/theorems/ec3873d0-f90c-4a9b-a47a-e24cb00d5019
-- title:
--   Division step
-- statement:
--   **Division step**: a two-term expansion of the numerator `muNum` transfers to `μ̃`, because
--   `kernelMass n = 1 + O(1/n)` (`kernelMass_sub_one_rate`).  Reduces the μ̃ expansion to a pure
--   numerator expansion.
--
--   The full literal source contract is:
--
--   ```lean
--   lemma muTilde_expansion_of_muNum {c₀ c₁ : ℝ}
--       (hnum : ∃ A : ℝ, 0 < A ∧ ∀ᶠ n : ℕ in atTop,
--         |muNum n - (c₀ + c₁ / Real.sqrt (n : ℝ))| ≤ A / (n : ℝ)) :
--       ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
--         |muTilde n - (c₀ + c₁ / Real.sqrt (n : ℝ))| ≤ K / (n : ℝ)
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/MuTilde.lean#L47. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_KernelBarriers
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MuTilde
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MuTilde_x1
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

open Filter Topology

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.muTilde_expansion_of_muNum {c₀ c₁ : ℝ}
    (hnum : ∃ A : ℝ, 0 < A ∧ ∀ᶠ n : ℕ in atTop,
      |muNum n - (c₀ + c₁ / Real.sqrt (n : ℝ))| ≤ A / (n : ℝ)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      |muTilde n - (c₀ + c₁ / Real.sqrt (n : ℝ))| ≤ K / (n : ℝ) := by sorry

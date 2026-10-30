-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_TanakaTelescope
-- name    : AnalyticCombinatorics_Ch8_Partitions_TanakaTelescope
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T11:16:01.619121+00:00
-- url     : https://prove2.me/theorems/a9a7cdb7-73e4-422d-9311-a1abbd8d5558
-- title:
--   Tanaka Telescope
-- statement:
--   The source mathematical objects and operations are specified by the following definitions.
--
--   ```lean
--   def distPow (K : ι → ι → ℝ) (μ0 : ι → ℝ) : ℕ → ι → ℝ
--     | 0 => μ0
--     | (t + 1) => fun z => ∑ x, distPow K μ0 t x * K x z
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/TanakaTelescope.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# R7 Fact B via Doeblin: Tanaka telescoping ⟹ window occupation lower bound

Telescoping the single-step `|D|`-drift (brick 85) over the evolving distribution `distPow K μ₀ t`
(the law of the walk after `t` steps) yields, for a mean-preserving bounded-increment kernel,

  `E|D_T| − E|D_0| ≤ b · ∑_{t<T} (window-occupation at step t)`,

i.e. `window-occupation ≥ (E|D_T| − E|D_0|)/b`.  Combined with the Paley–Zygmund bound `E|D_T| ≥ c√T`
(brick 84) and the per-step second/fourth moments of the Erdős rank-difference walk, this gives the
occupation lower bound `≥ 1/δ` that closes the Hardy–Ramanujan convergence.  All deterministic finite-sum
algebra.  Opus-authored.
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {ι : Type*} [Fintype ι]

/-- Law of the walk after `t` steps from initial distribution `μ₀` under kernel `K`. -/
def distPow (K : ι → ι → ℝ) (μ0 : ι → ℝ) : ℕ → ι → ℝ
  | 0 => μ0
  | (t + 1) => fun z => ∑ x, distPow K μ0 t x * K x z

end AnalyticCombinatorics.Ch8.Partitions.Erdos



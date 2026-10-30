-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_QVTelescope
-- name    : AnalyticCombinatorics_Ch8_Partitions_QVTelescope
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T11:26:22.800479+00:00
-- url     : https://prove2.me/theorems/dc72172f-1c7c-4dcd-92c0-8cb30f88b312
-- title:
--   Q V Telescope
-- statement:
--   The source mathematical objects and operations are specified by the following definitions.
--
--   ```lean
--   def locVar (K : ι → ι → ℝ) (D : ι → ℝ) (x : ι) : ℝ := ∑ z, K x z * (D z - D x) ^ 2
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/QVTelescope.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# R7 Fact B via Doeblin: quadratic-variation telescoping (Doob decomposition for `D²`)

For a mean-preserving kernel, `D²` has Doob compensator equal to the cumulative local variance
`locVar x = ∑_z K x z (D z − D x)²`:

  `E[D_T²] − E[D_0²] = ∑_{t<T} ∑_x distPow t x · locVar x`.

With a uniform local-variance lower bound `v₀ ≤ locVar` this gives `E[D_T²] ≥ E[D_0²] + v₀·T`, the lower
quadratic-variation feeding the Paley–Zygmund bound `E|D_T| ≥ c√T`.  Deterministic finite-sum.
Opus-authored.
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {ι : Type*} [Fintype ι]

/-- Local variance (one-step quadratic-variation increment) at `x`. -/
def locVar (K : ι → ι → ℝ) (D : ι → ℝ) (x : ι) : ℝ := ∑ z, K x z * (D z - D x) ^ 2

end AnalyticCombinatorics.Ch8.Partitions.Erdos



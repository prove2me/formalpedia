-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_erdos_limit_constant_of_renewal
-- name    : AnalyticCombinatorics.Ch8.Partitions.erdos_limit_constant_of_renewal
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T18:40:41.830433+00:00
-- url     : https://prove2.me/theorems/dadafb08-a67e-42f5-ac71-5798dc1e8e18
-- title:
--   Erdős–Hardy–Ramanujan limit constant, unconditional in the Riemann error
-- statement:
--   **Erdős–Hardy–Ramanujan limit constant, unconditional in the Riemann error.**
--   Given only the renewal/Tauberian input `u n → a` (`a > 0`), the constant is `1/(4√3)`.
--
--   The full literal source contract is:
--
--   ```lean
--   theorem erdos_limit_constant_of_renewal {a : ℝ} (ha : 0 < a)
--       (hlim : Tendsto Erdos.u atTop (𝓝 a)) :
--       a = 1 / (4 * Real.sqrt 3)
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/ErdosRiemannError.lean#L282. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Discharging the mesh-1 Riemann error (`RiemannErrorNegligible`)

The last hypothesis of `erdos_limit_constant`. We show the bracket-weighted error
integral is `o(mainScale)` by splitting `(0,∞)` at the saddle cutoff `x+1 = (C/4s)²`:

* on the right (`x+1 ≥ (C/4s)²`) the bracket `C/(2√(x+1)) − s − (x+1)⁻¹` is `≤ 2s`;
* on the left (`x+1 ≤ (C/4s)²`) the bracket is bounded by `C/2+s+1`, and the bulk
  `∫ saddleDensity` over that strip is `o(mainScale)` (same complete-square + the
  already-proved `gaussianTail_left_ratio_tendsto_zero`).
-/

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions

open Filter Topology BigOperators MeasureTheory Real
open AnalyticCombinatorics.Ch8.Partitions.Erdos
open scoped Topology Interval

theorem AnalyticCombinatorics.Ch8.Partitions.erdos_limit_constant_of_renewal {a : ℝ} (ha : 0 < a)
    (hlim : Tendsto Erdos.u atTop (𝓝 a)) :
    a = 1 / (4 * Real.sqrt 3) := by sorry

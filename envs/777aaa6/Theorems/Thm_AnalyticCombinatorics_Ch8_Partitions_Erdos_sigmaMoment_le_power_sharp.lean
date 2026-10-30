-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_sigmaMoment_le_power_sharp
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.sigmaMoment_le_power_sharp
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T16:17:46.30414+00:00
-- url     : https://prove2.me/theorems/15337b2e-e18e-49aa-a7f4-58a6fe9dbefb
-- title:
--   Sharp moment bound
-- statement:
--   **Sharp moment bound**: `M_r(t) ≤ K_r/t^{r+2}` on `0 < t ≤ 1`. Global dominator
--   `F(a) ≤ E·2^{r+1}(ρ^a/t^{r+1} + a^{r+1}ρ^a)` using `1−e^{−ta} ≥ ta/(1+ta)`.
--
--   The full literal source contract is:
--
--   ```lean
--   lemma sigmaMoment_le_power_sharp (r : ℕ) :
--       ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
--         sigmaMoment r t ≤ K / t ^ (r + 2)
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/MassRateMomentSharp.lean#L195. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateMoments
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Mass-rate campaign: the sharp moment bound `M_r(t) ≤ K_r/t^{r+2}`

The true leading order of `M_r(t) = Σ_m m^r σ(m) e^{−tm}` is `(r+1)!·ζ(2)/t^{r+2}`, sharper by
`1/t` than the crude `σ(m) ≤ m²` bound (`/t^{r+3}`).  Needed for the §5 `kernelMass_sub_approx2`
error terms (`M₃`, `M₄`).

Route: weighted divisor Fubini `M_r = Σ_a Σ_b a^{r+1} b^r ρ^{ab}` (ρ = e^{−t}), via
`_root_.sigmaAntidiagonalEquivProd` (`Σ_{ab=e} a^{r+1} b^r = e^r σ(e)`); the summand is dominated by
`ρ^{−1}·(a^{r+1}ρ^a)(b^r ρ^b)` (since `ab ≥ a+b−1`).  Opus-authored.
-/

set_option maxHeartbeats 1000000

open Filter Finset ArithmeticFunction
open scoped BigOperators Topology ArithmeticFunction.sigma

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.sigmaMoment_le_power_sharp (r : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
      sigmaMoment r t ≤ K / t ^ (r + 2) := by sorry

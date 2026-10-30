-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_sigmaMoment_one_two_term
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.sigmaMoment_one_two_term
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T17:22:02.538739+00:00
-- url     : https://prove2.me/theorems/6e1bb0ff-7bbe-41e2-941c-369eeff4790a
-- title:
--   Moment-one two-term asymptotic
-- statement:
--   **Moment-one two-term asymptotic.**
--   `|M₁(t) − (2(π²/6)/t³ − 1/(2t²))| ≤ K/t` for `0 < t < 1`.
--
--   The full literal source contract is:
--
--   ```lean
--   theorem sigmaMoment_one_two_term :
--       ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 0 < t → t < 1 →
--         |sigmaMoment 1 t - (2 * (Real.pi ^ 2 / 6) / t ^ 3 - 1 / (2 * t ^ 2))| ≤ K / t
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/MassRateMomentOneTwoTerm.lean#L330. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateMoments
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Mass-rate campaign: the **two-term** moment-one asymptotic

The weak version (`sigmaMoment_one_asymp_weak`) gives only the leading term
`M₁(t) = 2(π²/6)/t³ + O(1/t²)`.  Here we extract the next order:

  `M₁(t) = 2(π²/6)/t³ − 1/(2t²) + O(1/t)`,  i.e.  `|M₁(t) − (2(π²/6)/t³ − 1/(2t²))| ≤ K/t`.

The `−1/(2t²)` term is **not** a pointwise singularity of `boseKernel2`; it is the
Riemann-sum main term of the regularized derivative.  Writing
`M₁(t) = 2(π²/6)/t³ − Σ_{k≥1} k·boseReg0′(tk)` (the weak split), the remainder sum is
`(1/t)·Σ_{k≥1} G(tk)` with `G(x) = x·boseReg0′(x)`, and the general Riemann estimate
(`riemann_sum_Ioi_sub_integral_bound`) gives `Σ_{k≥1} G(tk) = (1/t)·∫₀^∞ G + O(1)`.
The integral is `∫₀^∞ x·boseReg0′(x) dx = 1/2`, computed via `G = (x·boseReg0)′ − boseReg0`
and `∫₀^∞ boseReg0 = −1/2` with vanishing boundary terms.  Hence
`Σ_{k≥1} k·boseReg0′(tk) = 1/(2t²) + O(1/t)`.  Opus-authored (ChatGPT R14 route, repo-verified).
-/

set_option maxHeartbeats 1600000

open Filter MeasureTheory Set
open scoped Topology

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.sigmaMoment_one_two_term :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 0 < t → t < 1 →
      |sigmaMoment 1 t - (2 * (Real.pi ^ 2 / 6) / t ^ 3 - 1 / (2 * t ^ 2))| ≤ K / t := by sorry

-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_sigmaMoment_nonneg
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.sigmaMoment_nonneg
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T16:17:23.583009+00:00
-- url     : https://prove2.me/theorems/f4785216-2038-4ed1-a86a-2a537a3ccc55
-- title:
--   Supporting lemma: sigmaMoment nonneg
-- statement:
--   `sigmaMoment r t ≥ 0` for `t > 0` (all summands are nonnegative).
--
--   The full literal source contract is:
--
--   ```lean
--   lemma sigmaMoment_nonneg (r : ℕ) (t : ℝ) (ht : 0 < t) : 0 ≤ sigmaMoment r t
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/MuNumExpansion.lean#L139. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateMoments
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# MuNum two-term expansion

`|muNum n − (μ̄ + μA/√n)| ≤ K/n` for large `n`, where
`μ̄ = 3/massLam` and `μA = 3/(2·massLam²)`.
-/

set_option maxHeartbeats 4000000

open Filter Finset
open scoped Topology BigOperators

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos

/-! ### Algebraic expansion of the model product -/

/-! ### Model sum expressed via sigma moments (infinite-sum identity) -/

/-! ### Small lemmas -/

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.sigmaMoment_nonneg (r : ℕ) (t : ℝ) (ht : 0 < t) : 0 ≤ sigmaMoment r t := by sorry

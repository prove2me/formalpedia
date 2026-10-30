-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_abs_smooth_sub_le_rnk_add_one
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.abs_smooth_sub_le_rnk_add_one
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T13:09:44.582398+00:00
-- url     : https://prove2.me/theorems/984ab889-dcfa-45db-8cac-043c0434b5f0
-- title:
--   Comparison of square-root scale with floored rank
-- statement:
--   A deterministic comparison of smooth3sqrt(n) and its floored rank; not a drift or variance production theorem.
--
--   The full literal source contract is:
--
--   ```lean
--   lemma abs_smooth_sub_le_rnk_add_one (x y : ℕ) :
--       |3 * Real.sqrt x - 3 * Real.sqrt y|
--         ≤ ((Int.natAbs ((rnk x : ℤ) - (rnk y : ℤ))) : ℝ) + 1
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/SmoothScale.lean#L18. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_KernelBarriers
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_PartitionRenewal
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# R7 Fact B via Doeblin: smooth scale vs floored rank

The floored rank `rnk n = ⌊3√n⌋` is NOT an approximate martingale (the fractional part `frac(3√n)`
contributes an `Θ(1)` phase obstruction).  The smooth scale `3√n` IS, so the occupation/Tanaka argument
runs on the smooth difference `3√x − 3√y`; the window is transferred back to the `rnk`-window with a
constant `+1` slack, since `|3√x − 3√y| ≤ |rnk x − rnk y| + 1`.  Opus-authored.
-/

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.abs_smooth_sub_le_rnk_add_one (x y : ℕ) :
    |3 * Real.sqrt x - 3 * Real.sqrt y|
      ≤ ((Int.natAbs ((rnk x : ℤ) - (rnk y : ℤ))) : ℝ) + 1 := by sorry

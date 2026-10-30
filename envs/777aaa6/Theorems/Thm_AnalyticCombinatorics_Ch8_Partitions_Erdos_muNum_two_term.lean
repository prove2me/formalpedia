-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_muNum_two_term
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.muNum_two_term
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T19:09:05.584989+00:00
-- url     : https://prove2.me/theorems/369cacf9-4150-41fc-b29a-c8c0ac3aa5a5
-- title:
--   The numerator has the required two-term expansion
-- statement:
--   The numerator has the required two-term expansion.
--
--   The full literal source contract is:
--
--   ```lean
--   theorem muNum_two_term :
--       ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
--         |muNum n - (3 / massLam + (3 / (2 * massLam ^ 2)) / Real.sqrt (n : ℝ))|
--         ≤ K / (n : ℝ)
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/MuNumAssembly.lean#L10. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateMoments
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MuTilde
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Assembly of the two-term expansion for `muNum`

This file only assembles the banked estimates:

* the infinite model two-term expansion,
* the two main-range errors,
* the weighted Erdős far tail,
* and a local model-product tail.
-/

open Filter Finset
open scoped Topology BigOperators

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.muNum_two_term :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      |muNum n - (3 / massLam + (3 / (2 * massLam ^ 2)) / Real.sqrt (n : ℝ))|
      ≤ K / (n : ℝ) := by sorry

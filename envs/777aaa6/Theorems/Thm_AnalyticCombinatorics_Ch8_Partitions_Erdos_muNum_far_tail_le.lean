-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_muNum_far_tail_le
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.muNum_far_tail_le
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T17:21:54.600698+00:00
-- url     : https://prove2.me/theorems/e8e293d9-c6e2-4a13-86fd-dcb96d5fd370
-- title:
--   The far muNum tail follows from the weighted Erdős tail
-- statement:
--   The far `muNum` tail follows from the weighted Erdős tail.
--
--   The full literal source contract is:
--
--   ```lean
--   theorem muNum_far_tail_le :
--       ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
--         (∑ m ∈ Finset.Icc (⌊(n : ℝ) ^ (2 / 3 : ℝ)⌋₊ + 1) (n - 1),
--           erdosWeight n m * rhoDrop n m) ≤ K / (n : ℝ)
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/MuNumAssembly.lean#L10. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
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

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.muNum_far_tail_le :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      (∑ m ∈ Finset.Icc (⌊(n : ℝ) ^ (2 / 3 : ℝ)⌋₊ + 1) (n - 1),
        erdosWeight n m * rhoDrop n m) ≤ K / (n : ℝ) := by sorry

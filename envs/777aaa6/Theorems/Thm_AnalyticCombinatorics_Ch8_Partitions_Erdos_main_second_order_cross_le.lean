-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_main_second_order_cross_le
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.main_second_order_cross_le
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T17:47:19.061836+00:00
-- url     : https://prove2.me/theorems/01252c5e-4459-484a-a16f-53b78193bff5
-- title:
--   The second-order cross term on the main range
-- statement:
--   The second-order cross term on the main range.
--
--   The full literal source contract is:
--
--   ```lean
--   theorem main_second_order_cross_le :
--       ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
--         (∑ m ∈ Finset.Icc 1 ⌊(n : ℝ) ^ (2 / 3 : ℝ)⌋₊,
--           |erdosWeight n m - modelSummand n m| * |rhoDrop n m - rhoDropModel n m|)
--         ≤ K / (n : ℝ)
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/MuNumAssembly.lean#L10. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MuNumModel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateMoments
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MuTilde
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateApprox2
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

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.main_second_order_cross_le :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      (∑ m ∈ Finset.Icc 1 ⌊(n : ℝ) ^ (2 / 3 : ℝ)⌋₊,
        |erdosWeight n m - modelSummand n m| * |rhoDrop n m - rhoDropModel n m|)
      ≤ K / (n : ℝ) := by sorry

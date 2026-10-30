-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_model_rhoDropModel_tail_le
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.model_rhoDropModel_tail_le
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T17:21:58.92519+00:00
-- url     : https://prove2.me/theorems/6860f7fc-e687-4513-9632-390c017a6880
-- title:
--   The model-product tail past the n^(2/3) cutoff
-- statement:
--   The model-product tail past the `n^(2/3)` cutoff.
--
--   The full literal source contract is:
--
--   ```lean
--   theorem model_rhoDropModel_tail_le :
--       ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
--         (∑' m : ℕ,
--           if m ≤ ⌊(n : ℝ) ^ (2 / 3 : ℝ)⌋₊ then (0 : ℝ)
--           else |modelSummand n m * rhoDropModel n m|)
--         ≤ K / (n : ℝ)
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/MuNumAssembly.lean#L10. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MuNumModel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateMoments
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

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.model_rhoDropModel_tail_le :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      (∑' m : ℕ,
        if m ≤ ⌊(n : ℝ) ^ (2 / 3 : ℝ)⌋₊ then (0 : ℝ)
        else |modelSummand n m * rhoDropModel n m|)
      ≤ K / (n : ℝ) := by sorry

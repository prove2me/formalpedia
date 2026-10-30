-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_model_rhoDropModel_tsum_split
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.model_rhoDropModel_tsum_split
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T18:16:22.266228+00:00
-- url     : https://prove2.me/theorems/5381b3df-9ba1-4ed4-8779-353a124ef41e
-- title:
--   Supporting lemma: model rhoDropModel tsum split
-- statement:
--   Supporting lemma from AnalyticCombinatorics/Ch8/Partitions/MuNumAssembly.lean.
--
--   The full literal source contract is:
--
--   ```lean
--   lemma model_rhoDropModel_tsum_split (n M : ℕ) (hn : 1 ≤ n) :
--       (∑' m : ℕ, if m = 0 then (0 : ℝ) else modelSummand n m * rhoDropModel n m)
--         = (∑ m ∈ Finset.Icc 1 M, modelSummand n m * rhoDropModel n m)
--           + (∑' m : ℕ,
--               if m ≤ M then (0 : ℝ)
--               else if m = 0 then (0 : ℝ) else modelSummand n m * rhoDropModel n m)
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/MuNumAssembly.lean#L518. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

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

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.model_rhoDropModel_tsum_split (n M : ℕ) (hn : 1 ≤ n) :
    (∑' m : ℕ, if m = 0 then (0 : ℝ) else modelSummand n m * rhoDropModel n m)
      = (∑ m ∈ Finset.Icc 1 M, modelSummand n m * rhoDropModel n m)
        + (∑' m : ℕ,
            if m ≤ M then (0 : ℝ)
            else if m = 0 then (0 : ℝ) else modelSummand n m * rhoDropModel n m) := by sorry

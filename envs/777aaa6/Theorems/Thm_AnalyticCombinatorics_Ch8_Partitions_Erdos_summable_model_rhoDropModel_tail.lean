-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_summable_model_rhoDropModel_tail
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.summable_model_rhoDropModel_tail
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T17:47:11.051999+00:00
-- url     : https://prove2.me/theorems/78b03bf6-b99f-4a7c-9a43-c4f62d92c902
-- title:
--   Supporting lemma: summable model rhoDropModel tail
-- statement:
--   Supporting lemma from AnalyticCombinatorics/Ch8/Partitions/MuNumAssembly.lean.
--
--   The full literal source contract is:
--
--   ```lean
--   lemma summable_model_rhoDropModel_tail {n M : ℕ} (hn : 1 ≤ n) :
--       Summable (fun m : ℕ =>
--         if m ≤ M then (0 : ℝ)
--         else if m = 0 then (0 : ℝ) else modelSummand n m * rhoDropModel n m)
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/MuNumAssembly.lean#L501. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

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

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.summable_model_rhoDropModel_tail {n M : ℕ} (hn : 1 ≤ n) :
    Summable (fun m : ℕ =>
      if m ≤ M then (0 : ℝ)
      else if m = 0 then (0 : ℝ) else modelSummand n m * rhoDropModel n m) := by sorry

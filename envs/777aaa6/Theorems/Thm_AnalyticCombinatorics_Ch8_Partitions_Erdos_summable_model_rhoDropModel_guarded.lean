-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_summable_model_rhoDropModel_guarded
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.summable_model_rhoDropModel_guarded
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T17:21:43.876711+00:00
-- url     : https://prove2.me/theorems/0b76677b-4ab8-447f-9b43-f0f1a8f0a51e
-- title:
--   Supporting lemma: summable model rhoDropModel guarded
-- statement:
--   Supporting lemma from AnalyticCombinatorics/Ch8/Partitions/MuNumAssembly.lean.
--
--   The full literal source contract is:
--
--   ```lean
--   lemma summable_model_rhoDropModel_guarded {n : ℕ} (hn : 1 ≤ n) :
--       Summable (fun m : ℕ =>
--         if m = 0 then (0 : ℝ) else modelSummand n m * rhoDropModel n m)
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/MuNumAssembly.lean#L467. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

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

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.summable_model_rhoDropModel_guarded {n : ℕ} (hn : 1 ≤ n) :
    Summable (fun m : ℕ =>
      if m = 0 then (0 : ℝ) else modelSummand n m * rhoDropModel n m) := by sorry

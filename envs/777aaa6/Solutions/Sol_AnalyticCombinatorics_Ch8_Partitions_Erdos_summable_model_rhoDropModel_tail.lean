-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.summable_model_rhoDropModel_tail
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T17:47:58.844164+00:00
-- url     : https://prove2.me/submissions/e9a34aac-10e1-4876-94b3-ca8e7b87c891

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MuNumModel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateMoments
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateApprox2
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_summable_model_rhoDropModel_guarded
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

noncomputable section

open Filter Finset
open scoped Topology BigOperators

end

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos
open Filter Finset
open scoped Topology BigOperators
theorem solution {n M : ℕ} (hn : 1 ≤ n) :
    Summable (fun m : ℕ =>
      if m ≤ M then (0 : ℝ)
      else if m = 0 then (0 : ℝ) else modelSummand n m * rhoDropModel n m) := by
  have hsumm := summable_model_rhoDropModel_guarded (n := n) hn
  have hheadsumm : Summable (fun m : ℕ =>
      if m ≤ M then (if m = 0 then (0 : ℝ) else modelSummand n m * rhoDropModel n m)
      else 0) :=
    summable_of_ne_finset_zero (s := Finset.range (M + 1)) (fun b hb => by
      rw [Finset.mem_range] at hb
      rw [if_neg (by omega : ¬ b ≤ M)])
  refine (hsumm.sub hheadsumm).congr ?_
  intro m
  by_cases hm : m ≤ M
  · simp [hm]
  · simp [hm]

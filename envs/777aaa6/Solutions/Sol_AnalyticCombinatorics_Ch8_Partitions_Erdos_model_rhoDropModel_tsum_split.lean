-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.model_rhoDropModel_tsum_split
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T18:17:33.22962+00:00
-- url     : https://prove2.me/submissions/025685c1-7e11-4b95-9b8f-2ffd4a114701

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MuNumModel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateMoments
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateApprox2
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_summable_model_rhoDropModel_guarded
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_summable_model_rhoDropModel_tail
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
theorem solution (n M : ℕ) (hn : 1 ≤ n) :
    (∑' m : ℕ, if m = 0 then (0 : ℝ) else modelSummand n m * rhoDropModel n m)
      = (∑ m ∈ Finset.Icc 1 M, modelSummand n m * rhoDropModel n m)
        + (∑' m : ℕ,
            if m ≤ M then (0 : ℝ)
            else if m = 0 then (0 : ℝ) else modelSummand n m * rhoDropModel n m) := by
  have hsumm := summable_model_rhoDropModel_guarded (n := n) hn
  have hheadsumm : Summable (fun m : ℕ =>
      if m ≤ M then (if m = 0 then (0 : ℝ) else modelSummand n m * rhoDropModel n m)
      else 0) :=
    summable_of_ne_finset_zero (s := Finset.range (M + 1)) (fun b hb => by
      rw [Finset.mem_range] at hb
      rw [if_neg (by omega : ¬ b ≤ M)])
  have htailsumm := summable_model_rhoDropModel_tail (n := n) (M := M) hn
  have hhead : (∑' m : ℕ,
      if m ≤ M then (if m = 0 then (0 : ℝ) else modelSummand n m * rhoDropModel n m)
      else 0)
      = ∑ m ∈ Finset.Icc 1 M, modelSummand n m * rhoDropModel n m := by
    rw [tsum_eq_sum (s := Finset.Icc 1 M) (fun b hb => by
      rw [Finset.mem_Icc] at hb
      by_cases hbM : b ≤ M
      · have hb0 : b = 0 := by omega
        simp [hb0]
      · simp [hbM])]
    refine Finset.sum_congr rfl ?_
    intro m hm
    rw [Finset.mem_Icc] at hm
    rw [if_pos hm.2, if_neg (by omega : m ≠ 0)]
  rw [← hhead, ← hheadsumm.tsum_add htailsumm]
  apply tsum_congr
  intro m
  by_cases hm : m ≤ M
  · simp [hm]
  · simp [hm]

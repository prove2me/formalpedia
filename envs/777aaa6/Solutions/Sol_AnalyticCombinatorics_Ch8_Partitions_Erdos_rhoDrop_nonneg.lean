-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.rhoDrop_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T16:19:20.592211+00:00
-- url     : https://prove2.me/submissions/d83bd1bf-b9ff-49d7-8834-1bd9d6332bc8

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

noncomputable section

open Filter Finset
open scoped Topology BigOperators

end

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos
open Filter Finset
open scoped Topology BigOperators
theorem solution {n m : ℕ} (_hm : m ≤ n) :
    0 ≤ rhoDrop n m := by
  rw [rhoDrop]
  have hsqrt : Real.sqrt (((n - m : ℕ) : ℝ)) ≤ Real.sqrt (n : ℝ) := by
    apply Real.sqrt_le_sqrt
    exact_mod_cast Nat.sub_le n m
  nlinarith

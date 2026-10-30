-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.muNum_split_main_tail
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T16:19:08.149348+00:00
-- url     : https://prove2.me/submissions/7435b20c-b968-4175-9c5f-b629018128eb

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
theorem solution (n M : ℕ) (hMle : M ≤ n - 1) :
    muNum n =
      (∑ m ∈ Finset.Icc 1 M, erdosWeight n m * rhoDrop n m)
      + (∑ m ∈ Finset.Icc (M + 1) (n - 1), erdosWeight n m * rhoDrop n m) := by
  have e1 : Finset.Icc 1 M = Finset.Ioc 0 M := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have e2 : Finset.Icc (M + 1) (n - 1) = Finset.Ioc M (n - 1) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have e3 : Finset.Icc 1 (n - 1) = Finset.Ioc 0 (n - 1) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [muNum, e1, e2, e3, Finset.sum_Ioc_consecutive _ (Nat.zero_le M) hMle]

-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.muTilde_two_term
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T19:33:30.242168+00:00
-- url     : https://prove2.me/submissions/9386f097-dd15-446e-9937-dfb2d33db257

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_KernelBarriers
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateMoments
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MuTilde
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MuTilde_x1
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_muNum_two_term
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_muTilde_expansion_of_muNum
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
theorem solution :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      |muTilde n - (3 / massLam + (3 / (2 * massLam ^ 2)) / Real.sqrt (n : ℝ))|
      ≤ K / (n : ℝ) := by
  exact muTilde_expansion_of_muNum muNum_two_term

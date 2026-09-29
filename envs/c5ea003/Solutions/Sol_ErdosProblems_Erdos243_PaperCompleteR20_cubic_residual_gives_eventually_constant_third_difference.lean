-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR20.cubic_residual_gives_eventually_constant_third_difference
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:48:37.85099+00:00
-- url     : https://prove2.me/submissions/68caa448-ea95-4854-86d4-898cc144f99c

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateFiniteDifference
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDifferenceLimits
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_fourth_int_difference_tendsto_zero_of_cubic_residual
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_third_difference_eventually_constant_of_fourth_tendsto_zero
import Mathlib

/-!
# Erdős 243: limit transport for the cubic finite-difference extraction

The paper's analytic comparison produces a residual whose first forward
difference tends to zero.  This file proves that this is exactly enough for
the fourth difference of the integer numerator to tend to zero, because the
rising cubic has identically zero fourth difference.
-/

noncomputable section

namespace ErdosProblems.Erdos243.PaperCompleteR20
open Filter
end ErdosProblems.Erdos243.PaperCompleteR20

open Filter
open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR20 in
theorem solution
    (C : ℕ → ℤ) (K : ℝ) (r : ℕ → ℝ)
    (hdecomp : (fun n => (C n : ℝ)) = fun n => K * risingCubic n + r n)
    (hr : Tendsto (realForwardDiff r) atTop (nhds 0)) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      iterIntForwardDiff 3 C n = iterIntForwardDiff 3 C N :=
  third_difference_eventually_constant_of_fourth_tendsto_zero C
    (fourth_int_difference_tendsto_zero_of_cubic_residual C K r hdecomp hr)

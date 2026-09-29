-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR20.iterRealForwardDiff_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T23:01:53.259115+00:00
-- url     : https://prove2.me/submissions/59465d75-c446-4e27-ab20-d87429c85ca5

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateFiniteDifference
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDifferenceLimits
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_realForwardDiff_tendsto_zero
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
    {u : ℕ → ℝ} (hu : Tendsto u atTop (nhds 0)) :
    ∀ k : ℕ, Tendsto (iterRealForwardDiff k u) atTop (nhds 0)
  | 0 => hu
  | k + 1 => realForwardDiff_tendsto_zero (solution hu k)

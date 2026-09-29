-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR20.realForwardDiff_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T22:52:33.723415+00:00
-- url     : https://prove2.me/submissions/989eb74a-4cb7-43b0-a78c-d5c8b5a99a8f

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateFiniteDifference
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDifferenceLimits
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
    Tendsto (realForwardDiff u) atTop (nhds 0) := by
  simpa [realForwardDiff, Function.comp_def] using
    (hu.comp (tendsto_add_atTop_nat 1)).sub hu

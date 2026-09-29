-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR20.iterRealForwardDiff_succ
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T22:50:58.710734+00:00
-- url     : https://prove2.me/submissions/0b4bdbd0-0a3d-468d-9bf9-29343affd99d

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
@[simp] theorem solution (k : ℕ) (u : ℕ → ℝ) :
    iterRealForwardDiff (k + 1) u = realForwardDiff (iterRealForwardDiff k u) := rfl

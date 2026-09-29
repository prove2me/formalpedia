-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR20.iterIntForwardDiff_cast
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T22:59:50.457855+00:00
-- url     : https://prove2.me/submissions/752225d2-88c1-4c8a-a2bb-7c92d983ae44

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateFiniteDifference
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDifferenceLimits
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_iterIntForwardDiff_succ
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_iterRealForwardDiff_succ
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
theorem solution (k : ℕ) (u : ℕ → ℤ) (n : ℕ) :
    (iterIntForwardDiff k u n : ℝ) =
      iterRealForwardDiff k (fun j => (u j : ℝ)) n := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
      simp only [iterIntForwardDiff_succ, iterRealForwardDiff_succ, intForwardDiff,
        realForwardDiff, Int.cast_sub, ih]

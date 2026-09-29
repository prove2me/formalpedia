-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR20.iterRealForwardDiff_const_mul
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T23:01:51.312697+00:00
-- url     : https://prove2.me/submissions/4ccb56cb-234c-49ac-b4a1-940523e41230

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateFiniteDifference
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDifferenceLimits
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
theorem solution (k : ℕ) (c : ℝ) (u : ℕ → ℝ) :
    iterRealForwardDiff k (fun n => c * u n) =
      fun n => c * iterRealForwardDiff k u n := by
  induction k with
  | zero => rfl
  | succ k ih =>
      funext n
      simp only [iterRealForwardDiff_succ, realForwardDiff, ih]
      ring

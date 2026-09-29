-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR20.iterRealForwardDiff_add
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T22:59:51.923703+00:00
-- url     : https://prove2.me/submissions/01c1f6f5-62a8-480c-b662-363b5f935fda

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
theorem solution (k : ℕ) (u v : ℕ → ℝ) :
    iterRealForwardDiff k (fun n => u n + v n) =
      fun n => iterRealForwardDiff k u n + iterRealForwardDiff k v n := by
  induction k with
  | zero => rfl
  | succ k ih =>
      funext n
      simp only [iterRealForwardDiff_succ, realForwardDiff, ih]
      ring

-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR20.fourth_int_difference_tendsto_zero_of_cubic_residual
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T23:09:20.195813+00:00
-- url     : https://prove2.me/submissions/444a3a62-772f-4bf0-859b-e6ef1d63d89c

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateFiniteDifference
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDifferenceLimits
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_iterIntForwardDiff_cast
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_iterRealForwardDiff_add
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_iterRealForwardDiff_const_mul
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_iterRealForwardDiff_tendsto_zero
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





















theorem fourth_difference_risingCubic (n : ℕ) :
    iterRealForwardDiff 4 risingCubic n = 0 := by
  norm_num [iterRealForwardDiff, realForwardDiff, risingCubic]
  ring
end ErdosProblems.Erdos243.PaperCompleteR20

open Filter
open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR20 in
theorem solution
    (C : ℕ → ℤ) (K : ℝ) (r : ℕ → ℝ)
    (hdecomp : (fun n => (C n : ℝ)) = fun n => K * risingCubic n + r n)
    (hr : Tendsto (realForwardDiff r) atTop (nhds 0)) :
    Tendsto (fun n => (iterIntForwardDiff 4 C n : ℝ)) atTop (nhds 0) := by
  have hres : Tendsto (iterRealForwardDiff 3 (realForwardDiff r)) atTop (nhds 0) :=
    iterRealForwardDiff_tendsto_zero hr 3
  have hcubic : iterRealForwardDiff 4 (fun n => K * risingCubic n) = 0 := by
    rw [iterRealForwardDiff_const_mul]
    funext n
    simp [fourth_difference_risingCubic]
  have hfour : iterRealForwardDiff 4 (fun n => (C n : ℝ)) =
      iterRealForwardDiff 4 r := by
    rw [hdecomp, iterRealForwardDiff_add, hcubic]
    funext n
    simp
  have hrfour : Tendsto (iterRealForwardDiff 4 r) atTop (nhds 0) := by
    simpa [iterRealForwardDiff] using hres
  simpa only [iterIntForwardDiff_cast, hfour] using hrfour

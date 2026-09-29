-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR20.cubic_residual_sublinear_of_normalisedCubicError
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:04:26.41718+00:00
-- url     : https://prove2.me/submissions/3889fc26-49a6-4486-b6fc-5471c7c63920

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateFiniteDifference
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDifferenceLimits
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateResidualStep
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDefect
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateNormalisation
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_risingCubic_div_cube_tendsto_one
import Mathlib

/-!
# Erdős 243: normalised cubic comparison

The remaining product-comparison estimate naturally says that the quotient by
the rising cubic converges to its limit with error `o(n^-2)`.  This file proves
that this single estimate supplies both normalisations required downstream.
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
    (C r : ℕ → ℝ) (K : ℝ)
    (hdecomp : C = fun n => K * risingCubic n + r n)
    (herror : Tendsto (normalisedCubicError C K) atTop (nhds 0)) :
    Tendsto (fun n => r n / (n : ℝ)) atTop (nhds 0) := by
  have hprod : Tendsto
      (fun n => normalisedCubicError C K n *
        (risingCubic n / (n : ℝ) ^ 3)) atTop (nhds 0) := by
    simpa using herror.mul risingCubic_div_cube_tendsto_one
  apply hprod.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  simp only [normalisedCubicError, hdecomp]
  field_simp [risingCubic, hn.ne']
  ring

-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR20.realForwardDiff_residual_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:48:39.227946+00:00
-- url     : https://prove2.me/submissions/dcb40f92-a7ab-4956-920e-5258c390e3a2

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateFiniteDifference
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDifferenceLimits
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateResidualStep
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_realForwardDiff_residual_eq
import Mathlib

/-!
# Erdős 243: the cubic-rate residual recurrence

This is the exact algebraic step between the ratio comparison and the finite
difference argument.  The additive recurrence defect and the sublinear
residual together force the first residual difference to tend to zero.
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
    (hdefect : Tendsto (cubicAdditiveDefect C) atTop (nhds 0))
    (hsublinear : Tendsto (fun n => r n / (n : ℝ)) atTop (nhds 0)) :
    Tendsto (realForwardDiff r) atTop (nhds 0) := by
  have hsum : Tendsto
      (fun n => cubicAdditiveDefect C n + 3 * (r n / (n : ℝ)))
      atTop (nhds 0) := by
    simpa using hdefect.add (tendsto_const_nhds.mul hsublinear)
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact (realForwardDiff_residual_eq C r K hdecomp n hn).symm

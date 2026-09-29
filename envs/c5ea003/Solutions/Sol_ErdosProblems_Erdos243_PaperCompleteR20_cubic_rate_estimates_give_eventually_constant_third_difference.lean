-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR20.cubic_rate_estimates_give_eventually_constant_third_difference
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:04:24.953349+00:00
-- url     : https://prove2.me/submissions/84902249-ee61-4b93-b25a-cbc739a28d3d

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateFiniteDifference
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDifferenceLimits
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateResidualStep
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_cubic_residual_gives_eventually_constant_third_difference
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_realForwardDiff_residual_tendsto_zero
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
    (C : ℕ → ℤ) (K : ℝ) (r : ℕ → ℝ)
    (hdecomp : (fun n => (C n : ℝ)) = fun n => K * risingCubic n + r n)
    (hdefect : Tendsto (cubicAdditiveDefect (fun n => (C n : ℝ))) atTop (nhds 0))
    (hsublinear : Tendsto (fun n => r n / (n : ℝ)) atTop (nhds 0)) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      iterIntForwardDiff 3 C n = iterIntForwardDiff 3 C N := by
  apply cubic_residual_gives_eventually_constant_third_difference C K r hdecomp
  exact realForwardDiff_residual_tendsto_zero (fun n => (C n : ℝ)) r K
    hdecomp hdefect hsublinear

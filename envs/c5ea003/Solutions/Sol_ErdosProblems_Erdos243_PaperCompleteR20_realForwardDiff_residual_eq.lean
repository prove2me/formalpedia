-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR20.realForwardDiff_residual_eq
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T23:09:21.50615+00:00
-- url     : https://prove2.me/submissions/c5e1dd1f-8163-4c8c-ae37-689c69464331

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateFiniteDifference
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDifferenceLimits
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateResidualStep
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_risingCubic_ratio
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
    (n : ℕ) (hn : 0 < n) :
    realForwardDiff r n = cubicAdditiveDefect C n + 3 * (r n / (n : ℝ)) := by
  have hmodel := risingCubic_ratio n hn
  simp only [realForwardDiff, cubicAdditiveDefect, hdecomp]
  rw [hmodel]
  field_simp [hn.ne']
  ring

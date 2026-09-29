-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR20.risingCubic_ratio
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T22:50:56.862598+00:00
-- url     : https://prove2.me/submissions/9d7f0f94-4636-4bcf-94f6-2065670adc13

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateFiniteDifference
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDifferenceLimits
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateResidualStep
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
theorem solution (n : ℕ) (hn : 0 < n) :
    risingCubic (n + 1) = (1 + 3 / (n : ℝ)) * risingCubic n := by
  simp only [risingCubic]
  push_cast
  field_simp [hn.ne']
  ring

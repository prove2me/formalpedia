-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR20.normalisedCubicError_tendsto_zero_of_quotient_increment
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:04:28.814255+00:00
-- url     : https://prove2.me/submissions/f9ff0be9-af45-4dc3-9008-3ce071c6d6c2

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateFiniteDifference
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDifferenceLimits
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateResidualStep
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDefect
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateNormalisation
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateQuotientIncrement
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_exists_limit_with_square_scaled_tail
import Mathlib
import Mathlib.Analysis.PSeries

/-!
# Erdős 243: summing a cubic-rate increment

An increment which is `o(n⁻³)` has a convergent primitive whose tail is
`o(n⁻²)`.  This is the quantitative summation step needed for the literal
ratio error in the paper.
-/

noncomputable section

namespace ErdosProblems.Erdos243.PaperCompleteR20
open Filter Finset
end ErdosProblems.Erdos243.PaperCompleteR20

open Filter Finset
open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR20 in
theorem solution
    (C : ℕ → ℝ)
    (hincr : Tendsto (fun n : ℕ => (n : ℝ) ^ 3 *
      (cubicQuotient C (n + 1) - cubicQuotient C n)) atTop (nhds 0)) :
    ∃ K : ℝ, Tendsto (normalisedCubicError C K) atTop (nhds 0) := by
  simpa [normalisedCubicError, cubicQuotient] using
    exists_limit_with_square_scaled_tail (cubicQuotient C) hincr

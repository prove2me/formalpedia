-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR20.normalisedCubicError_of_literal_ratio_error
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:09:59.703917+00:00
-- url     : https://prove2.me/submissions/085ae761-c100-4b40-af15-aca538c601b2

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateFiniteDifference
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDifferenceLimits
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateResidualStep
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDefect
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateNormalisation
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateQuotientIncrement
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateQuotientBounded
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_cubicQuotient_eventually_bounded_of_ratio_error
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_cubicQuotient_increment_scaled_tendsto_zero
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_normalisedCubicError_tendsto_zero_of_quotient_increment
import Mathlib
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Erdős 243: the literal cubic product asymptotic

This module closes the analytic producer.  It starts with the paper's literal
scaled ratio error, proves the quotient bounded through the convergent product,
then sums the resulting quotient increments to the `o(n⁻²)` tail estimate.
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
    (C : ℕ → ℝ)
    (hC : ∀ᶠ n in atTop, C n ≠ 0)
    (hratio : Tendsto
      (fun n : ℕ => (n : ℝ) ^ 3 * cubicRatioError C n) atTop (nhds 0)) :
    ∃ K : ℝ, Tendsto (normalisedCubicError C K) atTop (nhds 0) := by
  have hbounded := cubicQuotient_eventually_bounded_of_ratio_error C hC hratio
  have hincr := cubicQuotient_increment_scaled_tendsto_zero C hC hbounded hratio
  exact normalisedCubicError_tendsto_zero_of_quotient_increment C hincr

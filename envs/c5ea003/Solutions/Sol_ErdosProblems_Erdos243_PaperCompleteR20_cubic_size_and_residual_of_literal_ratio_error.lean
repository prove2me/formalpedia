-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR20.cubic_size_and_residual_of_literal_ratio_error
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:17:34.907949+00:00
-- url     : https://prove2.me/submissions/36428eb6-4d23-4199-934d-7ed168f9e225

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateFiniteDifference
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDifferenceLimits
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateResidualStep
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDefect
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateNormalisation
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateQuotientIncrement
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateQuotientBounded
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_cubic_residual_sublinear_of_normalisedCubicError
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_cubic_size_tendsto_of_normalisedCubicError
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_normalisedCubicError_of_literal_ratio_error
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
    ∃ K : ℝ, ∃ r : ℕ → ℝ,
      C = (fun n : ℕ => K * risingCubic n + r n) ∧
      Tendsto (fun n : ℕ => C n / (n : ℝ) ^ 3) atTop (nhds K) ∧
      Tendsto (fun n : ℕ => r n / (n : ℝ)) atTop (nhds 0) := by
  obtain ⟨K, hK⟩ := normalisedCubicError_of_literal_ratio_error C hC hratio
  let r : ℕ → ℝ := fun n : ℕ => C n - K * risingCubic n
  have hdecomp : C = fun n : ℕ => K * risingCubic n + r n := by
    funext n
    simp [r]
  exact ⟨K, r, hdecomp,
    cubic_size_tendsto_of_normalisedCubicError C K hK,
    cubic_residual_sublinear_of_normalisedCubicError C r K hdecomp hK⟩

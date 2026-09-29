-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR20.literal_ratio_error_gives_eventually_constant_third_difference
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:21:39.467474+00:00
-- url     : https://prove2.me/submissions/f56893b1-1f37-43df-ae9c-eb90ec45597c

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateFiniteDifference
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDifferenceLimits
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateResidualStep
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDefect
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateNormalisation
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateQuotientIncrement
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateQuotientBounded
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_cubic_ratio_and_residual_estimates_give_eventually_constant_third_difference
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_cubic_size_and_residual_of_literal_ratio_error
import Mathlib
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Erdős 243: the integer endpoint of the cubic-rate argument

The literal multiplicative little-o hypothesis now reaches the discrete
conclusion directly: the third integer forward difference is eventually
constant.  All analytic limit and residual data are produced internally.
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
    (C : ℕ → ℤ)
    (hpos : ∀ n, 0 < C n)
    (hratio : Tendsto (fun n : ℕ => (n : ℝ) ^ 3 *
      cubicRatioError (fun j => (C j : ℝ)) n) atTop (nhds 0)) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      iterIntForwardDiff 3 C n = iterIntForwardDiff 3 C N := by
  have hC : ∀ᶠ n in atTop, (C n : ℝ) ≠ 0 := by
    filter_upwards [] with n
    exact_mod_cast (ne_of_gt (hpos n))
  obtain ⟨K, r, hdecomp, hcubic, hsublinear⟩ :=
    cubic_size_and_residual_of_literal_ratio_error
      (fun n : ℕ => (C n : ℝ)) hC hratio
  exact cubic_ratio_and_residual_estimates_give_eventually_constant_third_difference
    C K r hpos hdecomp hcubic hratio hsublinear

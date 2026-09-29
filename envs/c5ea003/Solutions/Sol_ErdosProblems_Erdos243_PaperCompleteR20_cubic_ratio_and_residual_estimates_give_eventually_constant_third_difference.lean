-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR20.cubic_ratio_and_residual_estimates_give_eventually_constant_third_difference
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:09:58.440762+00:00
-- url     : https://prove2.me/submissions/07dba030-6252-40be-9ac5-f717a302f22f

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateFiniteDifference
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDifferenceLimits
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateResidualStep
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDefect
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_cubicAdditiveDefect_tendsto_zero_of_ratioError
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_cubic_rate_estimates_give_eventually_constant_third_difference
import Mathlib

/-!
# Erdős 243: from ratio little-o to additive cubic defect

The paper states the rate multiplicatively.  This file records the exact
rescaling that converts its `o(n^-3)` error into an additive error tending to
zero once the numerator has cubic size.
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
    (hpos : ∀ n, 0 < C n)
    (hdecomp : (fun n => (C n : ℝ)) = fun n => K * risingCubic n + r n)
    (hcubic : Tendsto (fun n => (C n : ℝ) / (n : ℝ) ^ 3) atTop (nhds K))
    (hratio : Tendsto (fun n : ℕ => (n : ℝ) ^ 3 *
      cubicRatioError (fun j => (C j : ℝ)) n) atTop (nhds 0))
    (hsublinear : Tendsto (fun n => r n / (n : ℝ)) atTop (nhds 0)) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      iterIntForwardDiff 3 C n = iterIntForwardDiff 3 C N := by
  apply cubic_rate_estimates_give_eventually_constant_third_difference C K r hdecomp
  · apply cubicAdditiveDefect_tendsto_zero_of_ratioError (fun n => (C n : ℝ)) K
    · filter_upwards [] with n
      exact_mod_cast (ne_of_gt (hpos n))
    · exact hcubic
    · exact hratio
  · exact hsublinear

-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR20.literal_ratio_error_gives_exact_eventual_cubic
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:26:20.144832+00:00
-- url     : https://prove2.me/submissions/d8016105-d29b-4b57-8f2e-015b71085ed1

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateFiniteDifference
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDifferenceLimits
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateResidualStep
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDefect
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateNormalisation
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateQuotientIncrement
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateQuotientBounded
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_cubicAdditiveDefect_tendsto_zero_of_ratioError
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_realForwardDiff_residual_tendsto_zero
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_cubic_residual_eventually_constant
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_cubic_size_and_residual_of_literal_ratio_error
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_literal_ratio_error_gives_eventually_constant_third_difference
import Mathlib
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Erdős 243: exact eventual cubic profile

Once the integer third difference is constant, the residual's third
difference is constant as well.  Every positive-order difference of the
residual tends to zero, so descending through the differences makes the
residual itself eventually constant.
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
    ∃ K B : ℝ, ∃ N : ℕ, ∀ n, N ≤ n →
      (C n : ℝ) = K * risingCubic n + B := by
  have hC : ∀ᶠ n in atTop, (C n : ℝ) ≠ 0 := by
    filter_upwards [] with n
    exact_mod_cast (ne_of_gt (hpos n))
  obtain ⟨K, r, hdecomp, hcubic, hsublinear⟩ :=
    cubic_size_and_residual_of_literal_ratio_error
      (fun n : ℕ => (C n : ℝ)) hC hratio
  have hdefect := cubicAdditiveDefect_tendsto_zero_of_ratioError
    (fun n : ℕ => (C n : ℝ)) K hC hcubic hratio
  have hr := realForwardDiff_residual_tendsto_zero
    (fun n : ℕ => (C n : ℝ)) r K hdecomp hdefect hsublinear
  obtain ⟨N, hthird⟩ :=
    literal_ratio_error_gives_eventually_constant_third_difference C hpos hratio
  obtain ⟨N', hconst⟩ := cubic_residual_eventually_constant
    C K r N hdecomp hr hthird
  exact ⟨K, r N', N', fun n hn => by
    simpa only [hconst n hn] using congrFun hdecomp n⟩

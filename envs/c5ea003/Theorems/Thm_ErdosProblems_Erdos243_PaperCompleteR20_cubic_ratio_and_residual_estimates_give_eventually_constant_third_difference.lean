-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_cubic_ratio_and_residual_estimates_give_eventually_constant_third_difference
-- name    : ErdosProblems.Erdos243.PaperCompleteR20.cubic_ratio_and_residual_estimates_give_eventually_constant_third_difference
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-25T00:33:20.339948+00:00
-- url     : https://prove2.me/theorems/0385bf07-c498-4b15-ad2a-598e103951c6
-- title:
--   Lean source theorem: cubic_ratio_and_residual_estimates_give_eventually_constant_third_difference
-- statement:
--   If a positive integer sequence decomposes as C(n)=K·n(n+1)(n+2)+r(n), C(n)/n³ tends to K, its cubic model ratio error is o(n⁻³), and r(n)/n tends to zero, then its third forward integer difference is eventually constant.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR20/CubicRateDefect.lean#L50-L67
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1-L58
--   Paper's AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Original Erdős problem and Koizumi prior work are distinguished in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateFiniteDifference
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDifferenceLimits
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateResidualStep
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDefect
import Mathlib

/-!
# Erdős 243: from ratio little-o to additive cubic defect

The paper states the rate multiplicatively.  This file records the exact
rescaling that converts its `o(n^-3)` error into an additive error tending to
zero once the numerator has cubic size.
-/

noncomputable section


open Filter

open ErdosProblems.Erdos243.PaperCompleteR20

theorem ErdosProblems.Erdos243.PaperCompleteR20.cubic_ratio_and_residual_estimates_give_eventually_constant_third_difference
    (C : ℕ → ℤ) (K : ℝ) (r : ℕ → ℝ)
    (hpos : ∀ n, 0 < C n)
    (hdecomp : (fun n => (C n : ℝ)) = fun n => K * risingCubic n + r n)
    (hcubic : Tendsto (fun n => (C n : ℝ) / (n : ℝ) ^ 3) atTop (nhds K))
    (hratio : Tendsto (fun n : ℕ => (n : ℝ) ^ 3 *
      cubicRatioError (fun j => (C j : ℝ)) n) atTop (nhds 0))
    (hsublinear : Tendsto (fun n => r n / (n : ℝ)) atTop (nhds 0)) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      iterIntForwardDiff 3 C n = iterIntForwardDiff 3 C N := by sorry

-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_cubic_rate_estimates_give_eventually_constant_third_difference
-- name    : ErdosProblems.Erdos243.PaperCompleteR20.cubic_rate_estimates_give_eventually_constant_third_difference
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-25T00:33:23.832471+00:00
-- url     : https://prove2.me/theorems/aec9f8ae-ccea-46de-997e-f1dbb9ae8be8
-- title:
--   Lean source theorem: cubic_rate_estimates_give_eventually_constant_third_difference
-- statement:
--   If an integer sequence decomposes as C(n)=K·n(n+1)(n+2)+r(n), its additive cubic defect tends to zero, and r(n)/n tends to zero, then its third forward integer difference is constant from some index onward.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR20/CubicRateResidualStep.lean#L56-L67
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1-L58
--   Paper's AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Original Erdős problem and Koizumi prior work are distinguished in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110

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


open Filter

open ErdosProblems.Erdos243.PaperCompleteR20

theorem ErdosProblems.Erdos243.PaperCompleteR20.cubic_rate_estimates_give_eventually_constant_third_difference
    (C : ℕ → ℤ) (K : ℝ) (r : ℕ → ℝ)
    (hdecomp : (fun n => (C n : ℝ)) = fun n => K * risingCubic n + r n)
    (hdefect : Tendsto (cubicAdditiveDefect (fun n => (C n : ℝ))) atTop (nhds 0))
    (hsublinear : Tendsto (fun n => r n / (n : ℝ)) atTop (nhds 0)) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      iterIntForwardDiff 3 C n = iterIntForwardDiff 3 C N := by sorry

-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_cubic_residual_eventually_constant
-- name    : ErdosProblems.Erdos243.PaperCompleteR20.cubic_residual_eventually_constant
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-25T00:33:37.764539+00:00
-- url     : https://prove2.me/theorems/6771255d-1648-4cb6-9101-d80e025ec281
-- title:
--   Lean source theorem: cubic_residual_eventually_constant
-- statement:
--   If an integer sequence decomposes as C(n)=K·n(n+1)(n+2)+r(n), the forward difference r(n+1)−r(n) tends to zero, and C has constant third integer difference from index N onward, then r itself is constant from some index onward.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR20/CubicRateResidualConstant.lean#L45-L95
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1-L58
--   Paper's AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Original Erdős problem and Koizumi prior work are distinguished in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateFiniteDifference
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDifferenceLimits
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateResidualStep
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDefect
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateNormalisation
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateQuotientIncrement
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateQuotientBounded
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


open Filter

open ErdosProblems.Erdos243.PaperCompleteR20

theorem ErdosProblems.Erdos243.PaperCompleteR20.cubic_residual_eventually_constant
    (C : ℕ → ℤ) (K : ℝ) (r : ℕ → ℝ) (N : ℕ)
    (hdecomp : (fun n : ℕ => (C n : ℝ)) = fun n : ℕ => K * risingCubic n + r n)
    (hr : Tendsto (realForwardDiff r) atTop (nhds 0))
    (hthird : ∀ n, N ≤ n →
      iterIntForwardDiff 3 C n = iterIntForwardDiff 3 C N) :
    ∃ N' : ℕ, ∀ n, N' ≤ n → r n = r N' := by sorry

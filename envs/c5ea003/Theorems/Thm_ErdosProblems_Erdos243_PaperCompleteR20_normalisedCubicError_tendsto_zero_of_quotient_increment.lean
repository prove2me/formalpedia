-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_normalisedCubicError_tendsto_zero_of_quotient_increment
-- name    : ErdosProblems.Erdos243.PaperCompleteR20.normalisedCubicError_tendsto_zero_of_quotient_increment
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-25T00:45:39.840236+00:00
-- url     : https://prove2.me/theorems/1ed1557d-8545-4160-ba58-e7712c40109e
-- title:
--   Lean source theorem: normalisedCubicError_tendsto_zero_of_quotient_increment
-- statement:
--   If n³ times the increment of C(n)/[n(n+1)(n+2)] tends to zero, there is a real K for which n²(C(n)/[n(n+1)(n+2)]−K) tends to zero.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR20/CubicRateSummableTail.lean#L138-L146
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1-L58
--   Paper's AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Original Erdős problem and Koizumi prior work are distinguished in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateFiniteDifference
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDifferenceLimits
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateResidualStep
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDefect
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateNormalisation
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateQuotientIncrement
import Mathlib
import Mathlib.Analysis.PSeries

/-!
# Erdős 243: summing a cubic-rate increment

An increment which is `o(n⁻³)` has a convergent primitive whose tail is
`o(n⁻²)`.  This is the quantitative summation step needed for the literal
ratio error in the paper.
-/

noncomputable section


open Filter Finset

open ErdosProblems.Erdos243.PaperCompleteR20

theorem ErdosProblems.Erdos243.PaperCompleteR20.normalisedCubicError_tendsto_zero_of_quotient_increment
    (C : ℕ → ℝ)
    (hincr : Tendsto (fun n : ℕ => (n : ℝ) ^ 3 *
      (cubicQuotient C (n + 1) - cubicQuotient C n)) atTop (nhds 0)) :
    ∃ K : ℝ, Tendsto (normalisedCubicError C K) atTop (nhds 0) := by sorry

-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_exists_limit_with_square_scaled_tail
-- name    : ErdosProblems.Erdos243.PaperCompleteR20.exists_limit_with_square_scaled_tail
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-25T00:45:39.014008+00:00
-- url     : https://prove2.me/theorems/9c6baf95-5880-4cf4-8d61-988cdfcdd3d1
-- title:
--   Lean source theorem: exists_limit_with_square_scaled_tail
-- statement:
--   If n³ times the successive increment x(n+1)−x(n) tends to zero, then x has a real limit K and n²(x(n)−K) tends to zero.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR20/CubicRateSummableTail.lean#L53-L136
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

theorem ErdosProblems.Erdos243.PaperCompleteR20.exists_limit_with_square_scaled_tail
    (x : ℕ → ℝ)
    (hincr : Tendsto
      (fun n : ℕ => (n : ℝ) ^ 3 * (x (n + 1) - x n)) atTop (nhds 0)) :
    ∃ K : ℝ, Tendsto (fun n : ℕ => (n : ℝ) ^ 2 * (x n - K)) atTop (nhds 0) := by sorry

-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_tsum_one_div_cube_nat_add_le
-- name    : ErdosProblems.Erdos243.PaperCompleteR20.tsum_one_div_cube_nat_add_le
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T23:09:48.817967+00:00
-- url     : https://prove2.me/theorems/9042fa30-8cb3-43d9-9d3f-ec3794c411bc
-- title:
--   Lean source theorem: tsum_one_div_cube_nat_add_le
-- statement:
--   For every natural number n≥2, the infinite tail sum of 1/(n+k)³ over k≥0 is at most 1/n².
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR20/CubicRateSummableTail.lean#L18-L51
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

theorem ErdosProblems.Erdos243.PaperCompleteR20.tsum_one_div_cube_nat_add_le (n : ℕ) (hn : 2 ≤ n) :
    (∑' k : ℕ, 1 / ((n + k : ℕ) : ℝ) ^ 3) ≤ 1 / (n : ℝ) ^ 2 := by sorry

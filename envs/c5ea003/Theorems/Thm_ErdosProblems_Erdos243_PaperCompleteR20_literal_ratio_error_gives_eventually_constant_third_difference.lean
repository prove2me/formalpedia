-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_literal_ratio_error_gives_eventually_constant_third_difference
-- name    : ErdosProblems.Erdos243.PaperCompleteR20.literal_ratio_error_gives_eventually_constant_third_difference
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-25T00:46:06.580992+00:00
-- url     : https://prove2.me/theorems/646566e5-0fa6-48c0-a0e7-ec4fbffde66b
-- title:
--   Lean source theorem: literal_ratio_error_gives_eventually_constant_third_difference
-- statement:
--   If a positive integer-valued sequence has cubic-ratio error satisfying n³ times the error tending to zero, then its third integer forward difference is eventually constant.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR20/CubicRateProductEndpoint.lean#L17-L31
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
# Erdős 243: the integer endpoint of the cubic-rate argument

The literal multiplicative little-o hypothesis now reaches the discrete
conclusion directly: the third integer forward difference is eventually
constant.  All analytic limit and residual data are produced internally.
-/

noncomputable section


open Filter

open ErdosProblems.Erdos243.PaperCompleteR20

theorem ErdosProblems.Erdos243.PaperCompleteR20.literal_ratio_error_gives_eventually_constant_third_difference
    (C : ℕ → ℤ)
    (hpos : ∀ n, 0 < C n)
    (hratio : Tendsto (fun n : ℕ => (n : ℝ) ^ 3 *
      cubicRatioError (fun j => (C j : ℝ)) n) atTop (nhds 0)) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      iterIntForwardDiff 3 C n = iterIntForwardDiff 3 C N := by sorry

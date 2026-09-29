-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_fourth_int_difference_tendsto_zero_of_cubic_residual
-- name    : ErdosProblems.Erdos243.PaperCompleteR20.fourth_int_difference_tendsto_zero_of_cubic_residual
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T23:07:48.07101+00:00
-- url     : https://prove2.me/theorems/4dc5c060-f0c9-4400-8ab7-29aeb22301ea
-- title:
--   Lean source theorem: fourth_int_difference_tendsto_zero_of_cubic_residual
-- statement:
--   If an integer-valued sequence is K n(n+1)(n+2) plus a residual whose first real forward difference tends to zero, then its fourth integer forward difference, cast to the reals, tends to zero.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR20/CubicRateDifferenceLimits.lean#L80-L102
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1-L58
--   Paper's AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Original Erdős problem and Koizumi prior work are distinguished in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateFiniteDifference
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDifferenceLimits
import Mathlib

/-!
# Erdős 243: limit transport for the cubic finite-difference extraction

The paper's analytic comparison produces a residual whose first forward
difference tends to zero.  This file proves that this is exactly enough for
the fourth difference of the integer numerator to tend to zero, because the
rising cubic has identically zero fourth difference.
-/

noncomputable section


open Filter

open ErdosProblems.Erdos243.PaperCompleteR20

theorem ErdosProblems.Erdos243.PaperCompleteR20.fourth_int_difference_tendsto_zero_of_cubic_residual
    (C : ℕ → ℤ) (K : ℝ) (r : ℕ → ℝ)
    (hdecomp : (fun n => (C n : ℝ)) = fun n => K * risingCubic n + r n)
    (hr : Tendsto (realForwardDiff r) atTop (nhds 0)) :
    Tendsto (fun n => (iterIntForwardDiff 4 C n : ℝ)) atTop (nhds 0) := by sorry

-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_risingCubic_ratio
-- name    : ErdosProblems.Erdos243.PaperCompleteR20.risingCubic_ratio
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T22:49:28.841915+00:00
-- url     : https://prove2.me/theorems/c2a3f1ce-f82a-4fc4-8b11-d016bdc0e5c4
-- title:
--   Lean source theorem: risingCubic_ratio
-- statement:
--   For every positive n, the rising cubic satisfies (n+1)(n+2)(n+3)=(1+3/n)n(n+1)(n+2).
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR20/CubicRateResidualStep.lean#L21-L26
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

theorem ErdosProblems.Erdos243.PaperCompleteR20.risingCubic_ratio (n : ℕ) (hn : 0 < n) :
    risingCubic (n + 1) = (1 + 3 / (n : ℝ)) * risingCubic n := by sorry

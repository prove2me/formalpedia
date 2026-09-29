-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_realForwardDiff_residual_tendsto_zero
-- name    : ErdosProblems.Erdos243.PaperCompleteR20.realForwardDiff_residual_tendsto_zero
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-25T00:33:16.075592+00:00
-- url     : https://prove2.me/theorems/35594acf-a43f-4584-b06d-0ae6f0f7dce6
-- title:
--   Lean source theorem: realForwardDiff_residual_tendsto_zero
-- statement:
--   For C(n)=K n(n+1)(n+2)+r(n), if C's cubic additive defect and r(n)/n both tend to zero, then the forward difference of r tends to zero.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR20/CubicRateResidualStep.lean#L41-L54
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

theorem ErdosProblems.Erdos243.PaperCompleteR20.realForwardDiff_residual_tendsto_zero
    (C r : ℕ → ℝ) (K : ℝ)
    (hdecomp : C = fun n => K * risingCubic n + r n)
    (hdefect : Tendsto (cubicAdditiveDefect C) atTop (nhds 0))
    (hsublinear : Tendsto (fun n => r n / (n : ℝ)) atTop (nhds 0)) :
    Tendsto (realForwardDiff r) atTop (nhds 0) := by sorry

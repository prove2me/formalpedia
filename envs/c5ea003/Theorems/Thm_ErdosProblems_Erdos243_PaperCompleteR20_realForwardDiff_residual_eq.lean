-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_realForwardDiff_residual_eq
-- name    : ErdosProblems.Erdos243.PaperCompleteR20.realForwardDiff_residual_eq
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T23:07:42.966488+00:00
-- url     : https://prove2.me/theorems/7923b1e4-3bae-4a67-b2b9-3c99c5e5c85d
-- title:
--   Lean source theorem: realForwardDiff_residual_eq
-- statement:
--   For C(n)=K n(n+1)(n+2)+r(n) and n>0, the residual forward difference equals C's cubic additive defect plus 3r(n)/n.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR20/CubicRateResidualStep.lean#L28-L39
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

theorem ErdosProblems.Erdos243.PaperCompleteR20.realForwardDiff_residual_eq
    (C r : ℕ → ℝ) (K : ℝ)
    (hdecomp : C = fun n => K * risingCubic n + r n)
    (n : ℕ) (hn : 0 < n) :
    realForwardDiff r n = cubicAdditiveDefect C n + 3 * (r n / (n : ℝ)) := by sorry

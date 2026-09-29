-- Prove2me | Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateResidualStep
-- name    : ErdosProblems_Erdos243_PaperCompleteR20_CubicRateResidualStep
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-24T19:09:52.230311+00:00
-- url     : https://prove2.me/theorems/b6b574b5-ab61-454c-b2f7-5f6f389413dd
-- title:
--   Cubic additive defect
-- statement:
--   Defines cubicAdditiveDefect for a real sequence C at an index n; its exact expression is in the pinned source.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR20/CubicRateResidualStep.lean#L1-L72
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1-L58
--   Paper's AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Original Erdős problem and Koizumi prior work are distinguished in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateFiniteDifference
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDifferenceLimits
import Mathlib

/-!
# Erdős 243: the cubic-rate residual recurrence

This is the exact algebraic step between the ratio comparison and the finite
difference argument.  The additive recurrence defect and the sublinear
residual together force the first residual difference to tend to zero.
-/

noncomputable section

namespace ErdosProblems.Erdos243.PaperCompleteR20

open Filter

/-- The additive defect from the cubic model ratio `1 + 3/n`. -/
def cubicAdditiveDefect (C : ℕ → ℝ) (n : ℕ) : ℝ :=
  C (n + 1) - (1 + 3 / (n : ℝ)) * C n










end ErdosProblems.Erdos243.PaperCompleteR20



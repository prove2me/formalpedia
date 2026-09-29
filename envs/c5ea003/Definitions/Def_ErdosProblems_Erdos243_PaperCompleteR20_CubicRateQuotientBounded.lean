-- Prove2me | Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateQuotientBounded
-- name    : ErdosProblems_Erdos243_PaperCompleteR20_CubicRateQuotientBounded
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-24T19:47:57.109983+00:00
-- url     : https://prove2.me/theorems/178f37dd-1783-4e63-83cf-9bc64aeeed57
-- title:
--   Cubic relative error
-- statement:
--   Defines cubicRelativeError for a real sequence C at an index n; its exact expression is in the pinned source.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR20/CubicRateQuotientBounded.lean#L1-L114
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
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Erdős 243: boundedness of the cubic quotient

The literal `o(n⁻³)` relative error is summable.  Iterating the exact quotient
recurrence therefore expresses the quotient as a fixed initial value times a
convergent infinite-product prefix, which is eventually bounded.
-/

noncomputable section

namespace ErdosProblems.Erdos243.PaperCompleteR20

open Filter Finset

def cubicRelativeError (C : ℕ → ℝ) (n : ℕ) : ℝ :=
  cubicRatioError C n / (1 + 3 / (n : ℝ))










end ErdosProblems.Erdos243.PaperCompleteR20



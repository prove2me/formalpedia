-- Prove2me | Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateQuotientIncrement
-- name    : ErdosProblems_Erdos243_PaperCompleteR20_CubicRateQuotientIncrement
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-24T19:31:34.600248+00:00
-- url     : https://prove2.me/theorems/71e504fd-6922-4ff0-a4ef-9619370863d0
-- title:
--   Quotient by the rising cubic
-- statement:
--   Defines cubicQuotient(C,n) as C(n) divided by n(n + 1)(n + 2).
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR20/CubicRateQuotientIncrement.lean#L1-L60
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1-L58
--   Paper's AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Original Erdős problem and Koizumi prior work are distinguished in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateFiniteDifference
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDifferenceLimits
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateResidualStep
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDefect
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateNormalisation
import Mathlib

/-!
# Erdős 243: quotient increments at the cubic rate
-/

noncomputable section

namespace ErdosProblems.Erdos243.PaperCompleteR20

open Filter

def cubicQuotient (C : ℕ → ℝ) (n : ℕ) : ℝ := C n / risingCubic n








end ErdosProblems.Erdos243.PaperCompleteR20



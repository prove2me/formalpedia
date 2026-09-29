-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_risingCubic_div_cube_tendsto_one
-- name    : ErdosProblems.Erdos243.PaperCompleteR20.risingCubic_div_cube_tendsto_one
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T22:51:38.456908+00:00
-- url     : https://prove2.me/theorems/a2d87ebf-5f83-4d35-9321-efbacb745bc9
-- title:
--   Lean source theorem: risingCubic_div_cube_tendsto_one
-- statement:
--   The ratio n(n+1)(n+2)/n³ tends to one as n tends to infinity.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR20/CubicRateNormalisation.lean#L20-L36
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
# Erdős 243: normalised cubic comparison

The remaining product-comparison estimate naturally says that the quotient by
the rising cubic converges to its limit with error `o(n^-2)`.  This file proves
that this single estimate supplies both normalisations required downstream.
-/

noncomputable section


open Filter

open ErdosProblems.Erdos243.PaperCompleteR20

theorem ErdosProblems.Erdos243.PaperCompleteR20.risingCubic_div_cube_tendsto_one :
    Tendsto (fun n : ℕ => risingCubic n / (n : ℝ) ^ 3) atTop (nhds 1) := by sorry

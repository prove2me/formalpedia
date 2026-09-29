-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_cubic_size_tendsto_of_normalisedCubicError
-- name    : ErdosProblems.Erdos243.PaperCompleteR20.cubic_size_tendsto_of_normalisedCubicError
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-25T00:45:32.349947+00:00
-- url     : https://prove2.me/theorems/6063fc05-402f-401a-a296-ac3f10648ce3
-- title:
--   Lean source theorem: cubic_size_tendsto_of_normalisedCubicError
-- statement:
--   If n²(C(n)/[n(n+1)(n+2)]−K) tends to zero, then C(n)/n³ tends to K.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR20/CubicRateNormalisation.lean#L55-L71
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

theorem ErdosProblems.Erdos243.PaperCompleteR20.cubic_size_tendsto_of_normalisedCubicError
    (C : ℕ → ℝ) (K : ℝ)
    (herror : Tendsto (normalisedCubicError C K) atTop (nhds 0)) :
    Tendsto (fun n => C n / (n : ℝ) ^ 3) atTop (nhds K) := by sorry

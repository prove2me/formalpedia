-- Prove2me | Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateNormalisation
-- name    : ErdosProblems_Erdos243_PaperCompleteR20_CubicRateNormalisation
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-24T19:26:39.719982+00:00
-- url     : https://prove2.me/theorems/893ebe80-471d-43b3-9011-c98998ec1b44
-- title:
--   Normalised cubic error
-- statement:
--   Defines normalisedCubicError for a real sequence C, a real parameter K and an index n; its exact expression is in the pinned source.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR20/CubicRateNormalisation.lean#L1-L92
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1-L58
--   Paper's AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Original Erdős problem and Koizumi prior work are distinguished in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateFiniteDifference
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDifferenceLimits
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateResidualStep
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDefect
import Mathlib

/-!
# Erdős 243: normalised cubic comparison

The remaining product-comparison estimate naturally says that the quotient by
the rising cubic converges to its limit with error `o(n^-2)`.  This file proves
that this single estimate supplies both normalisations required downstream.
-/

noncomputable section

namespace ErdosProblems.Erdos243.PaperCompleteR20

open Filter

def normalisedCubicError (C : ℕ → ℝ) (K : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * (C n / risingCubic n - K)










end ErdosProblems.Erdos243.PaperCompleteR20



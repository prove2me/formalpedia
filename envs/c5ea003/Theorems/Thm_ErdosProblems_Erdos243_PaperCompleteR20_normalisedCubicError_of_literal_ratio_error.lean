-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_normalisedCubicError_of_literal_ratio_error
-- name    : ErdosProblems.Erdos243.PaperCompleteR20.normalisedCubicError_of_literal_ratio_error
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-25T00:45:38.789665+00:00
-- url     : https://prove2.me/theorems/069ca119-7488-4b71-a31c-1b0f98949dc9
-- title:
--   Lean source theorem: normalisedCubicError_of_literal_ratio_error
-- statement:
--   If C is eventually nonzero and n³ times its cubic-ratio error tends to zero, there is a real K for which n²(C(n)/[n(n+1)(n+2)]−K) tends to zero.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR20/CubicRateProductAsymptotic.lean#L18-L26
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1-L58
--   Paper's AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Original Erdős problem and Koizumi prior work are distinguished in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateFiniteDifference
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDifferenceLimits
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateResidualStep
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDefect
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateNormalisation
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateQuotientIncrement
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateQuotientBounded
import Mathlib
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Erdős 243: the literal cubic product asymptotic

This module closes the analytic producer.  It starts with the paper's literal
scaled ratio error, proves the quotient bounded through the convergent product,
then sums the resulting quotient increments to the `o(n⁻²)` tail estimate.
-/

noncomputable section


open Filter

open ErdosProblems.Erdos243.PaperCompleteR20

theorem ErdosProblems.Erdos243.PaperCompleteR20.normalisedCubicError_of_literal_ratio_error
    (C : ℕ → ℝ)
    (hC : ∀ᶠ n in atTop, C n ≠ 0)
    (hratio : Tendsto
      (fun n : ℕ => (n : ℝ) ^ 3 * cubicRatioError C n) atTop (nhds 0)) :
    ∃ K : ℝ, Tendsto (normalisedCubicError C K) atTop (nhds 0) := by sorry

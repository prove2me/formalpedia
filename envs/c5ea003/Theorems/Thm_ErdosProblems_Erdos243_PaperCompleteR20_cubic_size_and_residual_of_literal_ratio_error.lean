-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_cubic_size_and_residual_of_literal_ratio_error
-- name    : ErdosProblems.Erdos243.PaperCompleteR20.cubic_size_and_residual_of_literal_ratio_error
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-25T00:45:48.873523+00:00
-- url     : https://prove2.me/theorems/d1808c73-959b-4e18-974f-3e15a4b750ef
-- title:
--   Lean source theorem: cubic_size_and_residual_of_literal_ratio_error
-- statement:
--   If C is eventually nonzero and n³ times its cubic-ratio error tends to zero, then C has a decomposition K n(n+1)(n+2)+r(n) with C(n)/n³ tending to K and r(n)/n tending to zero.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR20/CubicRateProductAsymptotic.lean#L28-L44
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

theorem ErdosProblems.Erdos243.PaperCompleteR20.cubic_size_and_residual_of_literal_ratio_error
    (C : ℕ → ℝ)
    (hC : ∀ᶠ n in atTop, C n ≠ 0)
    (hratio : Tendsto
      (fun n : ℕ => (n : ℝ) ^ 3 * cubicRatioError C n) atTop (nhds 0)) :
    ∃ K : ℝ, ∃ r : ℕ → ℝ,
      C = (fun n : ℕ => K * risingCubic n + r n) ∧
      Tendsto (fun n : ℕ => C n / (n : ℝ) ^ 3) atTop (nhds K) ∧
      Tendsto (fun n : ℕ => r n / (n : ℝ)) atTop (nhds 0) := by sorry

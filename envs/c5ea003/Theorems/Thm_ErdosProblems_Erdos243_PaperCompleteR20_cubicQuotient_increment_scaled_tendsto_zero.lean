-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_cubicQuotient_increment_scaled_tendsto_zero
-- name    : ErdosProblems.Erdos243.PaperCompleteR20.cubicQuotient_increment_scaled_tendsto_zero
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T23:10:44.859562+00:00
-- url     : https://prove2.me/theorems/669c0662-15dd-4a8c-ae71-9d95db3765a4
-- title:
--   Lean source theorem: cubicQuotient_increment_scaled_tendsto_zero
-- statement:
--   For an eventually nonzero real sequence with eventually bounded normalized cubic quotient, if n³ times its cubic ratio error tends to zero, then n³ times each increment of that quotient tends to zero.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR20/CubicRateQuotientIncrement.lean#L31-L56
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

/-!
# Erdős 243: quotient increments at the cubic rate
-/

noncomputable section


open Filter

open ErdosProblems.Erdos243.PaperCompleteR20

theorem ErdosProblems.Erdos243.PaperCompleteR20.cubicQuotient_increment_scaled_tendsto_zero
    (C : ℕ → ℝ)
    (hC : ∀ᶠ n in atTop, C n ≠ 0)
    (hbounded : ∃ M : ℝ, ∀ᶠ n in atTop, |cubicQuotient C n| ≤ M)
    (hratio : Tendsto
      (fun n : ℕ => (n : ℝ) ^ 3 * cubicRatioError C n) atTop (nhds 0)) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ 3 *
      (cubicQuotient C (n + 1) - cubicQuotient C n)) atTop (nhds 0) := by sorry

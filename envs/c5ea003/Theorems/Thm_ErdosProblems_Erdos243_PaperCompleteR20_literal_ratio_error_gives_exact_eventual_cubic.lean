-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_literal_ratio_error_gives_exact_eventual_cubic
-- name    : ErdosProblems.Erdos243.PaperCompleteR20.literal_ratio_error_gives_exact_eventual_cubic
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-25T00:45:51.469723+00:00
-- url     : https://prove2.me/theorems/c204b838-3a24-4fb9-bb7a-648940dbd53d
-- title:
--   Lean source theorem: literal_ratio_error_gives_exact_eventual_cubic
-- statement:
--   If a positive integer-valued sequence has cubic-ratio error satisfying n³ times the error tending to zero, then it eventually equals K n(n+1)(n+2)+B for some real K and B.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR20/CubicRateResidualConstant.lean#L97-L119
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
# Erdős 243: exact eventual cubic profile

Once the integer third difference is constant, the residual's third
difference is constant as well.  Every positive-order difference of the
residual tends to zero, so descending through the differences makes the
residual itself eventually constant.
-/

noncomputable section


open Filter

open ErdosProblems.Erdos243.PaperCompleteR20

theorem ErdosProblems.Erdos243.PaperCompleteR20.literal_ratio_error_gives_exact_eventual_cubic
    (C : ℕ → ℤ)
    (hpos : ∀ n, 0 < C n)
    (hratio : Tendsto (fun n : ℕ => (n : ℝ) ^ 3 *
      cubicRatioError (fun j => (C j : ℝ)) n) atTop (nhds 0)) :
    ∃ K B : ℝ, ∃ N : ℕ, ∀ n, N ≤ n →
      (C n : ℝ) = K * risingCubic n + B := by sorry

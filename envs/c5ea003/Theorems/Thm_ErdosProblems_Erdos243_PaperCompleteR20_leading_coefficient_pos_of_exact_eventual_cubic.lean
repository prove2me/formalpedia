-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_leading_coefficient_pos_of_exact_eventual_cubic
-- name    : ErdosProblems.Erdos243.PaperCompleteR20.leading_coefficient_pos_of_exact_eventual_cubic
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-25T00:45:57.521165+00:00
-- url     : https://prove2.me/theorems/3f34f5b5-16d1-43fb-8664-37e4af66ad01
-- title:
--   Lean source theorem: leading_coefficient_pos_of_exact_eventual_cubic
-- statement:
--   If a positive integer-valued sequence is eventually exactly K n(n+1)(n+2)+B, and n³ times its cubic-ratio error tends to zero, then K is strictly positive.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR20/CubicRatePositiveRationalProfile.lean#L18-L72
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
# Erdős 243: positivity of the rational cubic coefficient

The eventual cubic obtained from the literal ratio estimate has a nonnegative
leading coefficient because the original sequence is positive.  Vanishing of
that coefficient would make the sequence eventually constant, contradicting
the same literal ratio estimate at scale `n^3`.
-/

noncomputable section


open Filter

open ErdosProblems.Erdos243.PaperCompleteR20

theorem ErdosProblems.Erdos243.PaperCompleteR20.leading_coefficient_pos_of_exact_eventual_cubic
    (C : ℕ → ℤ) (K B : ℝ) (N : ℕ)
    (hpos : ∀ n, 0 < C n)
    (hprofile : ∀ n, N ≤ n → (C n : ℝ) = K * risingCubic n + B)
    (hratio : Tendsto (fun n : ℕ => (n : ℝ) ^ 3 *
      cubicRatioError (fun j => (C j : ℝ)) n) atTop (nhds 0)) :
    0 < K := by sorry

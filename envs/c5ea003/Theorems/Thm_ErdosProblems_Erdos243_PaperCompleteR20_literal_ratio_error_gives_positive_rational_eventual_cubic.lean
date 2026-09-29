-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_literal_ratio_error_gives_positive_rational_eventual_cubic
-- name    : ErdosProblems.Erdos243.PaperCompleteR20.literal_ratio_error_gives_positive_rational_eventual_cubic
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-25T00:46:15.79498+00:00
-- url     : https://prove2.me/theorems/111ff18a-17cb-4bf2-9dd6-dc00fdfc9512
-- title:
--   Lean source theorem: literal_ratio_error_gives_positive_rational_eventual_cubic
-- statement:
--   Under the same positive-integer and vanishing scaled cubic-ratio-error hypotheses, the eventual cubic profile has a strictly positive rational leading coefficient and a rational constant term.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR20/CubicRatePositiveRationalProfile.lean#L74-L114
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

theorem ErdosProblems.Erdos243.PaperCompleteR20.literal_ratio_error_gives_positive_rational_eventual_cubic
    (C : ℕ → ℤ)
    (hpos : ∀ n, 0 < C n)
    (hratio : Tendsto (fun n : ℕ => (n : ℝ) ^ 3 *
      cubicRatioError (fun j => (C j : ℝ)) n) atTop (nhds 0)) :
    ∃ A D : ℚ, 0 < A ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      (C n : ℝ) = (A : ℝ) * risingCubic n + (D : ℝ) := by sorry

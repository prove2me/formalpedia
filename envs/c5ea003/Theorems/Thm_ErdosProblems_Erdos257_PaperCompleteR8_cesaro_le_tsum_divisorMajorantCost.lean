-- Prove2me | Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_cesaro_le_tsum_divisorMajorantCost
-- name    : ErdosProblems.Erdos257.PaperCompleteR8.cesaro_le_tsum_divisorMajorantCost
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T22:07:40.086746+00:00
-- url     : https://prove2.me/theorems/1b8f2429-3aab-43af-b985-bcc41723b372
-- title:
--   Summable divisor costs bound a Cesàro average
-- statement:
--   Suppose nonnegative g(n) is bounded for each positive n by the sum of nonnegative divisor costs c(d), with ∑ c(d)/d finite. Then the average of g over 1,…,X for X>0 is at most ∑ c(d)/d.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos257/PaperCompleteR8/CountableCoverLogBudget.lean#L62-L106
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L1-L75
--   Paper's authorship and AI-use disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Erdős's earlier reciprocal-summable criterion is credited in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L104-L110

import Definitions.Def_ErdosProblems_Erdos257_CoverIndependentPeriodicMean
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR7_CoverKernel
import Mathlib
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace ErdosProblems.Erdos257.PaperCompleteR8
end ErdosProblems.Erdos257.PaperCompleteR8

/-!
# Countable positive-cover first logarithmic moment

A finite test support admits a finite subcover. The omitted frame weights
are retained as a subprobability inequality, so no renormalisation cost is
lost. Countable divisor majorants are truncated only at the actual finite
observation horizon; their reciprocal costs are bounded by their convergent
series. The endpoint assumes summability of the explicit total cover cost,
not the logarithmic obstruction it proves.
-/
noncomputable section
open Finset
open ErdosProblems.Erdos257.PaperCompleteR7

open ErdosProblems.Erdos257.PaperCompleteR8

theorem ErdosProblems.Erdos257.PaperCompleteR8.cesaro_le_tsum_divisorMajorantCost
    (g c : ℕ → ℝ) (X : ℕ) (hX : 0 < X)
    (hg : ∀ n, 0 ≤ g n) (hc : ∀ d, 0 < d → 0 ≤ c d)
    (hs : Summable (fun d : ℕ => c d / (d : ℝ)))
    (hmaj : ∀ n, 0 < n → g n ≤ ∑ d ∈ n.divisors, c d) :
    (∑ n ∈ Finset.Icc 1 X, g n) / X ≤ ∑' d : ℕ, c d / (d : ℝ) := by sorry
end

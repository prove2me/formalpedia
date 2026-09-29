-- Prove2me | Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_finite_subprobability_cover_log_pointwise
-- name    : ErdosProblems.Erdos257.PaperCompleteR8.finite_subprobability_cover_log_pointwise
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T22:10:25.172167+00:00
-- url     : https://prove2.me/theorems/df43db4e-d84c-4c9c-a7ea-787fef21e260
-- title:
--   Subprobability frame counts bound a logarithm
-- statement:
--   For a nonempty finite index set J with positive weights η_j summing to at most 1 and exponents 0<α_j≤1, if natural f is at most the sum of natural counts g_j, then e·log f is at most the displayed sum of g_j^α_j/[η_j^α_j(2^α_j−1)], under Lean's convention log 0=0.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos257/PaperCompleteR8/CountableCoverLogBudget.lean#L31-L60
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

theorem ErdosProblems.Erdos257.PaperCompleteR8.finite_subprobability_cover_log_pointwise (J : Finset ℕ) (η α : ℕ → ℝ)
    (f : ℕ) (g : ℕ → ℕ) (hJ : J.Nonempty)
    (hη : ∑ j ∈ J, η j ≤ 1) (hηpos : ∀ j ∈ J, 0 < η j)
    (hα : ∀ j ∈ J, 0 < α j ∧ α j ≤ 1)
    (hcover : f ≤ ∑ j ∈ J, g j) :
    Real.exp 1 * Real.log (f : ℝ) ≤
      ∑ j ∈ J, (g j : ℝ) ^ α j / (η j ^ α j) / ((2 : ℝ) ^ α j - 1) := by sorry
end

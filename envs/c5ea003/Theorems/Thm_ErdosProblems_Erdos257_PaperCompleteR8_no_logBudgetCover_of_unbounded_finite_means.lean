-- Prove2me | Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_no_logBudgetCover_of_unbounded_finite_means
-- name    : ErdosProblems.Erdos257.PaperCompleteR8.no_logBudgetCover_of_unbounded_finite_means
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T23:26:49.255265+00:00
-- url     : https://prove2.me/theorems/6d9b283a-a572-44f3-832e-97f329f9eff4
-- title:
--   Unbounded finite logarithmic means rule out log-budget covers
-- statement:
--   If finite subsets of A have finite logarithmic means exceeding every real threshold, then A admits no logarithmic-budget cover.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos257/PaperCompleteR8/OptimizedCoverBudget.lean#L65-L72
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L1-L75
--   Paper's authorship and AI-use disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Erdős's earlier reciprocal-summable criterion is credited in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L104-L110

import Definitions.Def_ErdosProblems_Erdos257_CoverIndependentPeriodicMean
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR7_CoverKernel
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_OptimizedCoverBudget
import Mathlib
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! # Optimizing the actual countable positive-cover cost

The admissible objects contain literal frames, divisor coefficients and the
paper's explicit summability hypotheses. Their costs are optimized only when
at least one admissible cover exists; the separate nonexistence theorem does
not assign a fictitious value to the real infimum of an empty set.
-/
noncomputable section

open ErdosProblems.Erdos257.PaperCompleteR8

theorem ErdosProblems.Erdos257.PaperCompleteR8.no_logBudgetCover_of_unbounded_finite_means (A : Set ℕ)
    (hlarge : ∀ R : ℝ, ∃ F : Finset ℕ, (F : Set ℕ) ⊆ A ∧
      ∃ X : ℕ, 0 < X ∧ R < finiteLogarithmicMean F X) :
    IsEmpty (LogBudgetCover A) := by sorry
end

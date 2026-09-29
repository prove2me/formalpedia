-- Prove2me | Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_finiteLogarithmicMean_le_cost
-- name    : ErdosProblems.Erdos257.PaperCompleteR8.finiteLogarithmicMean_le_cost
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T23:26:42.155882+00:00
-- url     : https://prove2.me/theorems/949324f4-e35a-4132-90be-09526abcea0d
-- title:
--   Log-budget cover bounds every finite logarithmic mean
-- statement:
--   If C is a logarithmic-budget cover of A, then for every finite F⊆A and positive X, the finite logarithmic mean of F at X is at most C's cost.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos257/PaperCompleteR8/OptimizedCoverBudget.lean#L41-L47
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

theorem ErdosProblems.Erdos257.PaperCompleteR8.finiteLogarithmicMean_le_cost {A : Set ℕ} (C : LogBudgetCover A)
    (F : Finset ℕ) (hFA : (F : Set ℕ) ⊆ A) (X : ℕ) (hX : 0 < X) :
    finiteLogarithmicMean F X ≤ C.cost := by sorry
end

-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR8.finiteLogarithmicMean_le_cost
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:05:15.168046+00:00
-- url     : https://prove2.me/submissions/3295de4f-3b25-4169-ac1e-6121ddfd29fd

import Definitions.Def_ErdosProblems_Erdos257_CoverIndependentPeriodicMean
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR7_CoverKernel
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_OptimizedCoverBudget
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_countable_cover_log_mean_le_cost
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

open ErdosProblems in
open ErdosProblems.Erdos257 in
open ErdosProblems.Erdos257.PaperCompleteR8 in
theorem solution {A : Set ℕ} (C : LogBudgetCover A)
    (F : Finset ℕ) (hFA : (F : Set ℕ) ⊆ A) (X : ℕ) (hX : 0 < X) :
    finiteLogarithmicMean F X ≤ C.cost := by
  exact countable_cover_log_mean_le_cost F C.frame C.weight C.exponent C.coefficient
    X hX C.weight_sum C.weight_positive C.exponent_bounds C.coefficient_nonneg
    C.column_summable (fun a ha => C.covers a (hFA ha)) C.majorises C.budget_summable
end

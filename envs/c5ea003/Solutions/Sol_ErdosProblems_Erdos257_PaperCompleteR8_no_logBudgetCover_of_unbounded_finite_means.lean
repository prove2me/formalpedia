-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR8.no_logBudgetCover_of_unbounded_finite_means
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:07:28.879226+00:00
-- url     : https://prove2.me/submissions/ef0157fc-842f-4715-a772-8f8bec557a9f

import Definitions.Def_ErdosProblems_Erdos257_CoverIndependentPeriodicMean
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR7_CoverKernel
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_OptimizedCoverBudget
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_finiteLogarithmicMean_le_cost
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
theorem solution (A : Set ℕ)
    (hlarge : ∀ R : ℝ, ∃ F : Finset ℕ, (F : Set ℕ) ⊆ A ∧
      ∃ X : ℕ, 0 < X ∧ R < finiteLogarithmicMean F X) :
    IsEmpty (LogBudgetCover A) := by
  refine ⟨fun C => ?_⟩
  obtain ⟨F, hFA, X, hX, hlargeX⟩ := hlarge C.cost
  exact (not_lt_of_ge (finiteLogarithmicMean_le_cost C F hFA X hX)) hlargeX
end

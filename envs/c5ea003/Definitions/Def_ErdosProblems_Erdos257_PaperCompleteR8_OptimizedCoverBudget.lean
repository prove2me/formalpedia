-- Prove2me | Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_OptimizedCoverBudget
-- name    : ErdosProblems_Erdos257_PaperCompleteR8_OptimizedCoverBudget
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-24T18:52:05.178998+00:00
-- url     : https://prove2.me/theorems/d54a6a12-ca79-437c-871b-d564745fc2b1
-- title:
--   Logarithmic-budget cover data
-- statement:
--   Defines LogBudgetCover with countable frames, positive weights summing to one, exponents, nonnegative divisor coefficients, a cover condition and summable budget; also defines its cost and finite logarithmic means.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos257/PaperCompleteR8/OptimizedCoverBudget.lean#L1-L75
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

/-! # Optimizing the actual countable positive-cover cost

The admissible objects contain literal frames, divisor coefficients and the
paper's explicit summability hypotheses. Their costs are optimized only when
at least one admissible cover exists; the separate nonexistence theorem does
not assign a fictitious value to the real infimum of an empty set.
-/
noncomputable section
namespace ErdosProblems.Erdos257.PaperCompleteR8

/-- The paper's arbitrary-weight positive-cover data on an actual support. -/
structure LogBudgetCover (A : Set ℕ) where
  frame : ℕ → Finset ℕ
  weight : ℕ → ℝ
  exponent : ℕ → ℝ
  coefficient : ℕ → ℕ → ℝ
  frame_positive : ∀ j, 0 ∉ frame j
  weight_positive : ∀ j, 0 < weight j
  weight_sum : HasSum weight 1
  exponent_bounds : ∀ j, 0 < exponent j ∧ exponent j ≤ 1
  coefficient_nonneg : ∀ j d, 0 < d → 0 ≤ coefficient j d
  column_summable : ∀ j, Summable (fun d : ℕ => coefficient j d / (d : ℝ))
  covers : ∀ a ∈ A, ∃ j, a ∈ frame j
  majorises : ∀ j n, 0 < n →
    (((frame j).filter (fun a => a ∣ n)).card : ℝ) ^ exponent j ≤
      ∑ d ∈ n.divisors, coefficient j d
  budget_summable : Summable (fun j =>
    (∑' d : ℕ, coefficient j d / (d : ℝ)) /
      (weight j ^ exponent j) / ((2 : ℝ) ^ exponent j - 1))

def LogBudgetCover.cost {A : Set ℕ} (C : LogBudgetCover A) : ℝ :=
  ∑' j, (∑' d : ℕ, C.coefficient j d / (d : ℝ)) /
    (C.weight j ^ C.exponent j) / ((2 : ℝ) ^ C.exponent j - 1)

def finiteLogarithmicMean (F : Finset ℕ) (X : ℕ) : ℝ :=
  (∑ n ∈ Finset.Icc 1 X,
    Real.exp 1 * Real.log ((F.filter (fun a => a ∣ n)).card : ℝ)) / X











end ErdosProblems.Erdos257.PaperCompleteR8
end



-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR8.summable_divisorFrameBudget
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:59:52.155262+00:00
-- url     : https://prove2.me/submissions/e0f8f3e2-152c-4f42-9ab9-8ea871b33f36

import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_DyadicDivisorFrames
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_PrimeHarmonicBlocks
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_DivisorFrameWeightedBudget
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_divisorFrameBudget_le_geometric
import Mathlib
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic

/-!
# Divisor-product masses and the separating host's weighted frame budget

The reciprocal divisor sum is computed from the actual prime product. Its
exponential upper bound and the prescribed harmonic scales give a summable
sequence of literal dyadic frame weights. Identifying these literal weights
with the finite-prime weighted term uses the odd-cofactor valuation identity;
the divergent logarithmic moment is a separate remaining step.
-/
noncomputable section

namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset
end ErdosProblems.Erdos257.PaperCompleteR8

open Finset
open ErdosProblems in
open ErdosProblems.Erdos257 in
open ErdosProblems.Erdos257.PaperCompleteR8 in
theorem solution (P : ℕ → Finset ℕ)
    (hP : ∀ k p, p ∈ P k → Nat.Prime p)
    (hS : ∀ k, (∑ p ∈ P k, (1 : ℝ) / p) ≤ (2 : ℝ) ^ k + 1) :
    Summable (fun k => divisorFrameBudget (P k) k) := by
  have hgeo : Summable (fun k : ℕ => 6 * (3 / 16 : ℝ) ^ k) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(3 / 16 : ℝ)‖ < 1)).mul_left 6
  apply Summable.of_nonneg_of_le _ (fun k => divisorFrameBudget_le_geometric (P k) k (hP k) (hS k)) hgeo
  intro k
  unfold divisorFrameBudget
  apply div_nonneg (sum_nonneg (fun d _ => by positivity))
  have hh : (1 : ℝ) ≤ 2 ^ (2 ^ (k + 2) : ℕ) := one_le_pow₀ (by norm_num)
  linarith
end

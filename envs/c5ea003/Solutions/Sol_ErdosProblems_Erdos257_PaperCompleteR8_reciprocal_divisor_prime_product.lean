-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR8.reciprocal_divisor_prime_product
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:53:05.977517+00:00
-- url     : https://prove2.me/submissions/c8ad600d-14d4-42e8-94f7-83d262430941

import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_DyadicDivisorFrames
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_PrimeHarmonicBlocks
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_DivisorFrameWeightedBudget
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_reciprocal_divisor_sum_eq
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_sum_divisors_prime_product
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
theorem solution (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
    (∑ d ∈ (P.prod id).divisors, (1 : ℝ) / d) =
      ∏ p ∈ P, (1 + (1 : ℝ) / p) := by
  have hM : 0 < P.prod id := prod_pos (fun p hp => (hP p hp).pos)
  rw [reciprocal_divisor_sum_eq _ hM]
  have hnum : (∑ d ∈ (P.prod id).divisors, (d : ℝ)) = ∏ p ∈ P, ((p : ℝ) + 1) := by
    have h := congrArg (fun n : ℕ => (n : ℝ))
      (sum_divisors_prime_product P hP)
    simpa only [Nat.cast_sum, Nat.cast_prod, Nat.cast_add, Nat.cast_one] using h
  have hden : ((P.prod id : ℕ) : ℝ) = ∏ p ∈ P, (p : ℝ) := by simp
  rw [hnum, hden, ← prod_div_distrib]
  apply prod_congr rfl
  intro p hp
  have hpne : (p : ℝ) ≠ 0 := by exact_mod_cast (hP p hp).ne_zero
  field_simp
end

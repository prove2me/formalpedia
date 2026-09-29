-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR8.dyadic_frame_literal_weight_sum
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:39:17.413232+00:00
-- url     : https://prove2.me/submissions/c4adca1b-0ce5-4f7e-bd2e-df601b93f9e8

import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_DyadicDivisorFrames
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_PrimeHarmonicBlocks
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_DivisorFrameWeightedBudget
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
theorem solution (M k : ℕ) :
    (∑ a ∈ dyadicDivisorFrame M k,
      ((2 : ℝ) ^ (k + 2)) / ((a : ℝ) * ((2 : ℝ) ^ (2 ^ (k + 2) : ℕ) - 1))) =
    (∑ d ∈ M.divisors, (1 : ℝ) / d) /
      ((2 : ℝ) ^ (2 ^ (k + 2) : ℕ) - 1) := by
  classical
  unfold dyadicDivisorFrame
  rw [sum_image]
  · rw [sum_div]
    apply sum_congr rfl
    intro d hd
    have hdne : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
    have hpow : (2 : ℝ) ^ (k + 2) ≠ 0 := by positivity
    have hn : (0 : ℕ) < 2 ^ (k + 2) := Nat.pow_pos (by decide)
    have hh : (1 : ℝ) < 2 ^ (2 ^ (k + 2) : ℕ) := one_lt_pow₀ (by norm_num) hn.ne'
    have hden : (2 : ℝ) ^ (2 ^ (k + 2) : ℕ) - 1 ≠ 0 := by linarith
    push_cast
    field_simp
    <;> ring
  · intro a ha b hb heq
    exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide)) heq
end

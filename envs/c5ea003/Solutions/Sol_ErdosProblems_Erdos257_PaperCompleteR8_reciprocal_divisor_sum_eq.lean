-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR8.reciprocal_divisor_sum_eq
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:41:44.963078+00:00
-- url     : https://prove2.me/submissions/974f1abe-b276-4327-9e2e-96102c6e4f8a

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
theorem solution (M : ℕ) (hM : 0 < M) :
    (∑ d ∈ M.divisors, (1 : ℝ) / d) =
      (∑ d ∈ M.divisors, (d : ℝ)) / (M : ℝ) := by
  have hMne : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  apply (eq_div_iff hMne).2
  calc
    _ = ∑ d ∈ M.divisors, (M : ℝ) / d := by
      rw [sum_mul]
      apply sum_congr rfl
      intro d hd
      ring
    _ = ∑ d ∈ M.divisors, ((M / d : ℕ) : ℝ) := by
      apply sum_congr rfl
      intro d hd
      exact (Nat.cast_div (Nat.dvd_of_mem_divisors hd)
        (by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne')).symm
    _ = _ := Nat.sum_div_divisors M (fun d : ℕ => (d : ℝ))
end

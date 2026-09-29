-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR8.sum_divisors_prime_product
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:41:43.366048+00:00
-- url     : https://prove2.me/submissions/4a46af9b-48f4-469e-a5bd-d98a23a59a2b

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
theorem solution (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
    (∑ d ∈ (P.prod id).divisors, d) = ∏ p ∈ P, (p + 1) := by
  classical
  revert hP
  induction P using Finset.induction_on with
  | empty => intro _; simp
  | @insert p P hp ih =>
    intro hP
    have hprime := hP p (mem_insert_self p P)
    have hrest : ∀ q ∈ P, Nat.Prime q := fun q hq => hP q (mem_insert_of_mem hq)
    have hcop : Nat.Coprime p (P.prod id) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro q hq
      apply hprime.coprime_iff_not_dvd.mpr
      intro hd
      have heq := (Nat.prime_dvd_prime_iff_eq hprime (hrest q hq)).mp hd
      exact hp (heq.symm ▸ hq)
    rw [prod_insert hp, prod_insert hp]
    change (∑ d ∈ (p * P.prod id).divisors, d) =
      (p + 1) * ∏ q ∈ P, (q + 1)
    rw [hcop.sum_divisors_mul, hprime.sum_divisors, ih hrest]
end

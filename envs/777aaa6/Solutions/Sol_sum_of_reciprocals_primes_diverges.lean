-- Prove2me | solution 1 for sum_of_reciprocals_primes_diverges
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T02:56:54.831259+00:00
-- url     : https://prove2.me/submissions/776b4e74-92a5-43d4-ab96-639cbf1a5ea7

import Mathlib.NumberTheory.SumPrimeReciprocals

open Filter
open scoped BigOperators

theorem solution :
    Tendsto (fun n : ℕ => ∑ p ∈ (Finset.range n).filter Nat.Prime, (1 : ℝ) / p)
      atTop atTop := by
  have hnonneg : ∀ n : ℕ,
      0 ≤ Set.indicator {p | Nat.Prime p} (fun p : ℕ => (1 : ℝ) / p) n := by
    intro n
    exact Set.indicator_nonneg (fun p hp => by positivity) n
  have ht := (not_summable_iff_tendsto_nat_atTop_of_nonneg hnonneg).mp
    not_summable_one_div_on_primes
  simpa [Finset.sum_filter, Set.indicator] using ht

#print axioms solution

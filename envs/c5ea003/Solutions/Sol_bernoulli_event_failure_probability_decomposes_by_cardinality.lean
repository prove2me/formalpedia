-- Prove2me | solution 1 for bernoulli_event_failure_probability_decomposes_by_cardinality
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-14T00:11:45.969092+00:00
-- url     : https://prove2.me/submissions/dfb74d6e-5768-4ffc-99ef-b484583adda8

import Theorems.Thm_bernoulli_event_failure_probability_decomposes_by_cardinality
import Theorems.Thm_bernoulli_event_success_probability_decomposes_by_cardinality
import Theorems.Thm_binomial_cardinality_probabilities_sum_to_one
import Theorems.Thm_bernoulli_event_failure_decomposition_from_success_decomposition

open MatrixCompletion

open scoped Classical BigOperators

/-- Derive the Bernoulli failure cardinality-mixture formula from the success
mixture, binomial total mass, and a purely algebraic conversion. -/
theorem solution
    {n₁ n₂ : ℕ} (p : ℝ)
    (Event : Finset (Fin n₁ × Fin n₂) → Prop) :
    0 ≤ p → p ≤ 1 →
    1 - bernoulliEventProb p Event =
      ∑ k ∈ Finset.range (n₁ * n₂ + 1),
        binomialCardinalityProb (n₁ * n₂) k p *
          (1 - fixedCardinalityEventProb k Event) := by
  intro hpNonneg hpLeOne
  have hSuccess :=
    bernoulli_event_success_probability_decomposes_by_cardinality
      p Event hpNonneg hpLeOne
  have hTotal :=
    binomial_cardinality_probabilities_sum_to_one
      (n₁ * n₂) p hpNonneg hpLeOne
  exact bernoulli_event_failure_decomposition_from_success_decomposition
    p Event hpNonneg hpLeOne hSuccess hTotal


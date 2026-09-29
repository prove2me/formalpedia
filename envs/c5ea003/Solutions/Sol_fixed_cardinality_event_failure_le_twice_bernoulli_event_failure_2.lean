-- Prove2me | solution 2 for fixed_cardinality_event_failure_le_twice_bernoulli_event_failure
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T04:19:46.066348+00:00
-- url     : https://prove2.me/submissions/1eaed83d-3e2e-4201-8c6e-99822bd0e526

import Mathlib.Tactic.Linarith
import Theorems.Thm_fixed_cardinality_event_failure_probability_antitone_of_event_mono
import Theorems.Thm_binomial_lower_tail_at_matrix_sample_mean_ge_half
import Theorems.Thm_bernoulli_event_failure_lower_bound_from_cardinality_failures
import Theorems.Thm_sample_ratio_between_zero_and_one

open MatrixCompletion

/-- Combine monotonicity of fixed-size failure probabilities, the binomial
lower-tail median bound, and the Bernoulli cardinality decomposition. -/
theorem solution
    {n₁ n₂ : ℕ} (m : ℕ)
    (Event : Finset (Fin n₁ × Fin n₂) → Prop) :
    0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
    (∀ Omega Omega' : Finset (Fin n₁ × Fin n₂),
      Omega ⊆ Omega' → Event Omega → Event Omega') →
    1 - fixedCardinalityEventProb m Event ≤
      2 *
        (1 - bernoulliEventProb
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) Event) := by
  intro hn₁ hn₂ hm hMono
  rcases sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm with
    ⟨hpNonneg, hpLeOne⟩
  have hFailureAntitone :
      ∀ k : ℕ, k ≤ m →
        1 - fixedCardinalityEventProb m Event ≤
          1 - fixedCardinalityEventProb k Event := by
    intro k hk
    exact fixed_cardinality_event_failure_probability_antitone_of_event_mono
      Event hMono k m hk hm
  have hLowerTail :=
    binomial_lower_tail_at_matrix_sample_mean_ge_half n₁ n₂ m hn₁ hn₂ hm
  have hHalfFailure :=
    bernoulli_event_failure_lower_bound_from_cardinality_failures
      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) m Event
      hpNonneg hpLeOne hm hFailureAntitone hLowerTail
  linarith


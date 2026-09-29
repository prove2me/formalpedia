-- Prove2me | solution 2 for bernoulli_event_failure_decomposition_from_success_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T03:56:19.576568+00:00
-- url     : https://prove2.me/submissions/122b0984-009e-4a96-96c0-4cc8af636a54

import Definitions.Def_matrix_completion_fixed_cardinality
import Mathlib.Tactic.Ring

open MatrixCompletion

open scoped Classical BigOperators

theorem solution
    {n₁ n₂ : ℕ} (p : ℝ)
    (Event : Finset (Fin n₁ × Fin n₂) → Prop) :
    0 ≤ p → p ≤ 1 →
    bernoulliEventProb p Event =
      ∑ k ∈ Finset.range (n₁ * n₂ + 1),
        binomialCardinalityProb (n₁ * n₂) k p *
          fixedCardinalityEventProb k Event →
    (∑ k ∈ Finset.range (n₁ * n₂ + 1),
        binomialCardinalityProb (n₁ * n₂) k p) = 1 →
    1 - bernoulliEventProb p Event =
      ∑ k ∈ Finset.range (n₁ * n₂ + 1),
        binomialCardinalityProb (n₁ * n₂) k p *
          (1 - fixedCardinalityEventProb k Event) := by
  intro _ _ hsuccess htotal
  rw [hsuccess]
  calc
    1 -
        ∑ k ∈ Finset.range (n₁ * n₂ + 1),
          binomialCardinalityProb (n₁ * n₂) k p *
            fixedCardinalityEventProb k Event =
        (∑ k ∈ Finset.range (n₁ * n₂ + 1),
          binomialCardinalityProb (n₁ * n₂) k p) -
        ∑ k ∈ Finset.range (n₁ * n₂ + 1),
          binomialCardinalityProb (n₁ * n₂) k p *
            fixedCardinalityEventProb k Event := by rw [htotal]
    _ =
      ∑ k ∈ Finset.range (n₁ * n₂ + 1),
        binomialCardinalityProb (n₁ * n₂) k p *
          (1 - fixedCardinalityEventProb k Event) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring

-- Prove2me | solution 1 for rademacher_expectation_monotone
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-21T04:50:43.373813+00:00
-- url     : https://prove2.me/submissions/2544a9a5-2099-4093-b5fd-dc8122234714

import Definitions.Def_matrix_completion_rademacher

open MatrixCompletion
open scoped Classical BigOperators

theorem solution :
    ∀ {n₁ n₂ : ℕ}
      (F G : Finset (Fin n₁ × Fin n₂) → ℝ),
      (∀ S, F S ≤ G S) →
      rademacherExpectation F ≤ rademacherExpectation G := by
  intro n₁ n₂ F G h
  unfold rademacherExpectation
  apply Finset.sum_le_sum
  intro S _
  have hw : 0 ≤ rademacherObservationWeight S := by
    unfold rademacherObservationWeight; positivity
  exact mul_le_mul_of_nonneg_left (h S) hw

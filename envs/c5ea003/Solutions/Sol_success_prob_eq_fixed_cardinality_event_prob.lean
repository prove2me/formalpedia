-- Prove2me | solution 1 for success_prob_eq_fixed_cardinality_event_prob
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-15T15:18:47.736631+00:00
-- url     : https://prove2.me/submissions/95920ba2-7f85-4326-b13b-4c4d9eeec55f

import Theorems.Thm_success_prob_eq_fixed_cardinality_event_prob

open MatrixCompletion

theorem solution
    {n₁ n₂ : ℕ} (m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ) :
    successProb m M =
      fixedCardinalityEventProb m (fun Omega => IsUniqueMinimizer Omega M) := by
  rfl


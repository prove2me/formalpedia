-- Prove2me | solution 1 for bernoulli_success_probability_mono
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-06-20T15:09:43.081868+00:00
-- url     : https://prove2.me/submissions/5e77e860-6827-4268-a14d-4518af05707c

import Definitions.Def_matrix_completion_bernoulli
open MatrixCompletion
open scoped Classical BigOperators

theorem solution
    {n₁ n₂ : ℕ} (p : ℝ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
    (Event : Finset (Fin n₁ × Fin n₂) → Prop) :
    0 ≤ p → p ≤ 1 →
    (∀ Omega, Event Omega → IsUniqueMinimizer Omega M) →
    bernoulliEventProb p Event ≤ bernoulliSuccessProb p M := by
  intro hp0 hp1 hAB
  have hw : ∀ Om : Finset (Fin n₁ × Fin n₂), 0 ≤ bernoulliObservationWeight p Om := by
    intro Om
    unfold bernoulliObservationWeight
    exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)
  unfold bernoulliSuccessProb bernoulliEventProb
  apply Finset.sum_le_sum
  intro Omega _
  by_cases hA : Event Omega
  · rw [if_pos hA, if_pos (hAB Omega hA)]
  · rw [if_neg hA]
    by_cases hB : IsUniqueMinimizer Omega M
    · rw [if_pos hB]; exact hw Omega
    · rw [if_neg hB]

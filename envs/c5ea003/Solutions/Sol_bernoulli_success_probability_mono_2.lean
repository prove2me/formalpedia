-- Prove2me | solution 2 for bernoulli_success_probability_mono
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-20T20:14:23.459797+00:00
-- url     : https://prove2.me/submissions/367a75ca-600b-45ff-af21-9924e03cb5fa

import Definitions.Def_matrix_completion_bernoulli

open MatrixCompletion

theorem solution
    {n₁ n₂ : ℕ} (p : ℝ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
    (Event : Finset (Fin n₁ × Fin n₂) → Prop) :
    0 ≤ p → p ≤ 1 →
    (∀ Omega, Event Omega → IsUniqueMinimizer Omega M) →
    bernoulliEventProb p Event ≤ bernoulliSuccessProb p M := by
  intro hp hp_one hEvent
  unfold bernoulliEventProb bernoulliSuccessProb
  apply Finset.sum_le_sum
  intro Omega _
  by_cases hA : Event Omega
  · have hB : IsUniqueMinimizer Omega M := hEvent Omega hA
    simp [hA, hB]
  · by_cases hB : IsUniqueMinimizer Omega M
    · have hweight : 0 ≤ bernoulliObservationWeight p Omega := by
        unfold bernoulliObservationWeight
        exact mul_nonneg (pow_nonneg hp _)
          (pow_nonneg (sub_nonneg.mpr hp_one) _)
      simp [hA, hB, hweight]
    · simp [hA, hB]


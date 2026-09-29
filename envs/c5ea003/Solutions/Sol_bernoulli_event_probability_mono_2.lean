-- Prove2me | solution 2 for bernoulli_event_probability_mono
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-20T20:14:23.144806+00:00
-- url     : https://prove2.me/submissions/8883233f-ee4c-4b55-838e-5287b29b0812

import Definitions.Def_matrix_completion_bernoulli

open MatrixCompletion

theorem solution
    {n₁ n₂ : ℕ} (p : ℝ)
    (EventA EventB : Finset (Fin n₁ × Fin n₂) → Prop) :
    0 ≤ p → p ≤ 1 →
    (∀ Omega, EventA Omega → EventB Omega) →
    bernoulliEventProb p EventA ≤ bernoulliEventProb p EventB := by
  intro hp hp_one hAB
  unfold bernoulliEventProb
  apply Finset.sum_le_sum
  intro Omega _
  by_cases hA : EventA Omega
  · have hB : EventB Omega := hAB Omega hA
    simp [hA, hB]
  · by_cases hB : EventB Omega
    · have hweight : 0 ≤ bernoulliObservationWeight p Omega := by
        unfold bernoulliObservationWeight
        exact mul_nonneg (pow_nonneg hp _)
          (pow_nonneg (sub_nonneg.mpr hp_one) _)
      simp [hA, hB, hweight]
    · simp [hA, hB]


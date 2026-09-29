-- Prove2me | solution 1 for talagrand_tangent_sampling_deviation_around_mean_raw_tail_with_expectation_le_one
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-25T04:03:23.854561+00:00
-- url     : https://prove2.me/submissions/53a75626-f295-492b-b00f-8371b51d9465
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_talagrand_tangent_sampling_absolute_deviation_raw_tail_with_expectation_le_one
import Theorems.Thm_bernoulli_event_probability_mono
import Theorems.Thm_sample_ratio_between_zero_and_one

open MatrixCompletion

/-!
Source: Candes--Recht, PDF p. 46, Appendix 9.1, Theorem 9.1 and equation
(9.2), plus PDF p. 19, Theorem 4.2 equation (4.10).

The source theorem gives an absolute-deviation Talagrand tail for
`|Z - E Z|`, where `Z` is the tangent sampling deviation.  The present node
only asks for the upper one-sided event `Z ≤ E Z + radius`, so the reduction is
the formal implication from the absolute event to the one-sided event, followed
by monotonicity of Bernoulli event probability.
-/
theorem solution :
    ∃ K c : ℝ, 0 < K ∧ 0 < c ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (S : SVD M r) (B : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              tangentSamplingDeviation Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤ 1 →
        TangentSamplingTalagrandIncrementBound S
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) B →
        TangentSamplingTalagrandVarianceBound S
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) B →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              TangentSamplingDeviationBound Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (bernoulliExpectation
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                    (fun Omega' =>
                      tangentSamplingDeviation Omega' S
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) +
                  K * Real.sqrt (B * (β * Real.log (↑(max n₁ n₂)))))) ≥
          1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  rcases talagrand_tangent_sampling_absolute_deviation_raw_tail_with_expectation_le_one with
    ⟨K, c, hK, hc, hAbs⟩
  refine ⟨K, c, hK, hc, ?_⟩
  intro β hβ n₁ n₂ r m M S B hn₁ hn₂ hr hm hEZ hIncrement hVariance
  let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
  let meanZ : ℝ :=
    bernoulliExpectation p (fun Omega' => tangentSamplingDeviation Omega' S p)
  let radius : ℝ := K * Real.sqrt (B * (β * Real.log (↑(max n₁ n₂))))
  have hAbsProb :
      bernoulliEventProb p
          (fun Omega =>
            |tangentSamplingDeviation Omega S p - meanZ| ≤ radius) ≥
        1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
    simpa [p, meanZ, radius] using
      hAbs β hβ n₁ n₂ r m M S B hn₁ hn₂ hr hm
        hEZ hIncrement hVariance
  rcases sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm with
    ⟨hpNonneg, hpLeOne⟩
  have hMono :
      bernoulliEventProb p
          (fun Omega =>
            |tangentSamplingDeviation Omega S p - meanZ| ≤ radius) ≤
        bernoulliEventProb p
          (fun Omega =>
            TangentSamplingDeviationBound Omega S p (meanZ + radius)) := by
    exact bernoulli_event_probability_mono p _ _ hpNonneg hpLeOne
      (fun Omega hOmega => by
        have hUpper :
            tangentSamplingDeviation Omega S p - meanZ ≤ radius :=
          (abs_le.mp hOmega).2
        have hOneSided :
            tangentSamplingDeviation Omega S p ≤ radius + meanZ :=
          sub_le_iff_le_add.mp hUpper
        simpa [TangentSamplingDeviationBound, add_comm, meanZ, radius] using hOneSided)
  exact le_trans hAbsProb hMono

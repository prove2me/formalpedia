-- Prove2me | solution 1 for talagrand_tangent_sampling_deviation_around_mean_raw_tail_pos_with_expectation_le_one
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-07-19T18:59:49.592023+00:00
-- url     : https://prove2.me/submissions/734ba240-5622-4db7-bbae-24ee7c9ede9f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_talagrand_tangent_sampling_absolute_deviation_raw_tail_pos_with_expectation_le_one
import Theorems.Thm_bernoulli_event_probability_mono
import Theorems.Thm_sample_ratio_between_zero_and_one

open MatrixCompletion

/-!
Source: Candes--Recht 2008, Appendix 9.1, PDF pp. 46--47, Theorem 9.1 and
equation (9.2), as used in Theorem 4.2, PDF p. 19, equation (4.10).

This is the formal bridge from the corrected absolute-deviation Talagrand tail
to the one-sided event `Z <= E Z + radius`.
-/

theorem solution :
    ∃ K c : ℝ, 0 < K ∧ 0 < c ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r) (B : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → 0 < m → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
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
  rcases talagrand_tangent_sampling_absolute_deviation_raw_tail_pos_with_expectation_le_one with
    ⟨K, c, hK, hc, hAbs⟩
  refine ⟨K, c, hK, hc, ?_⟩
  intro β hβ n₁ n₂ r m M μ₀ μ₁ S B hn₁ hn₂ hr hmpos hm hμ₀ hμ₁ hA0 hA1
    hExpectation hInc hVar
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
      hAbs β hβ n₁ n₂ r m M μ₀ μ₁ S B hn₁ hn₂ hr hmpos hm
        hμ₀ hμ₁ hA0 hA1 hExpectation hInc hVar
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
            tangentSamplingDeviation Omega S p ≤ meanZ + radius := by
          linarith
        simpa [TangentSamplingDeviationBound, meanZ, radius] using hOneSided)
  exact le_trans hAbsProb hMono

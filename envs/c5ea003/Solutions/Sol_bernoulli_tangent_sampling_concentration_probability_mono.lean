-- Prove2me | solution 1 for bernoulli_tangent_sampling_concentration_probability_mono
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-13T23:53:23.762403+00:00
-- url     : https://prove2.me/submissions/1ccf31e5-aa02-4cdc-b60b-265e04ecd4ed

import Theorems.Thm_bernoulli_tangent_sampling_concentration_probability_mono
import Theorems.Thm_bernoulli_event_probability_mono
import Theorems.Thm_tangent_sampling_concentration_mono

open MatrixCompletion

/-- Lift deterministic monotonicity of the concentration threshold to Bernoulli
event-probability monotonicity. -/
theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r)
    (p small large c β : ℝ) :
    0 ≤ p → p ≤ 1 →
    small ≤ large →
    bernoulliEventProb p
        (fun Omega => TangentSamplingConcentration Omega S p small) ≥
        1 - c * Real.rpow (↑(max n₁ n₂)) (-β) →
    bernoulliEventProb p
        (fun Omega => TangentSamplingConcentration Omega S p large) ≥
        1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hpNonneg hpLeOne hSmallLarge hProb
  have hMono :
      bernoulliEventProb p
          (fun Omega => TangentSamplingConcentration Omega S p small) ≤
        bernoulliEventProb p
          (fun Omega => TangentSamplingConcentration Omega S p large) :=
    bernoulli_event_probability_mono p
      (fun Omega => TangentSamplingConcentration Omega S p small)
      (fun Omega => TangentSamplingConcentration Omega S p large)
      hpNonneg hpLeOne
      (by
        intro Omega hConcentration
        exact tangent_sampling_concentration_mono
          Omega S p small large hpNonneg hSmallLarge hConcentration)
  exact le_trans hProb hMono


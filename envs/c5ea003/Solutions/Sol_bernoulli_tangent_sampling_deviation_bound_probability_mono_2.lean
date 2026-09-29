-- Prove2me | solution 2 for bernoulli_tangent_sampling_deviation_bound_probability_mono
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T03:11:24.397254+00:00
-- url     : https://prove2.me/submissions/3c0f0fc6-9488-40e9-ab9b-7677bcfdea1c

import Definitions.Def_matrix_completion_bernoulli
import Definitions.Def_matrix_completion_tangent
import Theorems.Thm_bernoulli_event_probability_mono
import Theorems.Thm_tangent_sampling_deviation_bound_mono

open MatrixCompletion

theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r)
    (p small large c β : ℝ) :
    0 ≤ p → p ≤ 1 →
    small ≤ large →
    bernoulliEventProb p
        (fun Omega => TangentSamplingDeviationBound Omega S p small) ≥
        1 - c * Real.rpow (↑(max n₁ n₂)) (-β) →
    bernoulliEventProb p
        (fun Omega => TangentSamplingDeviationBound Omega S p large) ≥
        1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hp hp_one hle hsmallprob
  have hmono :
      bernoulliEventProb p
          (fun Omega => TangentSamplingDeviationBound Omega S p small) ≤
        bernoulliEventProb p
          (fun Omega => TangentSamplingDeviationBound Omega S p large) := by
    exact bernoulli_event_probability_mono p _ _ hp hp_one
      (fun Omega hOmega =>
        tangent_sampling_deviation_bound_mono Omega S p small large hle hOmega)
  exact le_trans hsmallprob hmono


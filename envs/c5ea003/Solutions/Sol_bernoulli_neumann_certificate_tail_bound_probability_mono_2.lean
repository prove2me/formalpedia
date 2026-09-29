-- Prove2me | solution 2 for bernoulli_neumann_certificate_tail_bound_probability_mono
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T03:11:23.887499+00:00
-- url     : https://prove2.me/submissions/0239a893-69b3-495c-86b4-cbf6bd72240d

import Definitions.Def_matrix_completion_neumann
import Theorems.Thm_bernoulli_event_probability_mono
import Theorems.Thm_neumann_certificate_tail_spectral_bound_mono

open MatrixCompletion

theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r)
    (p : ℝ) (k0 : ℕ) (small large c β : ℝ) :
    0 ≤ p → p ≤ 1 →
    small ≤ large →
    bernoulliEventProb p
        (fun Omega => NeumannCertificateTailSpectralBound Omega S p k0 small) ≥
        1 - c * Real.rpow (↑(max n₁ n₂)) (-β) →
    bernoulliEventProb p
        (fun Omega => NeumannCertificateTailSpectralBound Omega S p k0 large) ≥
        1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hp hp_one hle hsmallprob
  have hmono :
      bernoulliEventProb p
          (fun Omega => NeumannCertificateTailSpectralBound Omega S p k0 small) ≤
        bernoulliEventProb p
          (fun Omega => NeumannCertificateTailSpectralBound Omega S p k0 large) := by
    exact bernoulli_event_probability_mono p _ _ hp hp_one
      (fun Omega hOmega =>
        neumann_certificate_tail_spectral_bound_mono S Omega p k0 small large hle hOmega)
  exact le_trans hsmallprob hmono


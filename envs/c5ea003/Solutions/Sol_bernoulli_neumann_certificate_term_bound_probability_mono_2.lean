-- Prove2me | solution 2 for bernoulli_neumann_certificate_term_bound_probability_mono
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T03:11:23.682416+00:00
-- url     : https://prove2.me/submissions/88f68ab2-16fa-474c-b087-aa852f7f4bb8

import Definitions.Def_matrix_completion_neumann
import Theorems.Thm_bernoulli_event_probability_mono
import Theorems.Thm_neumann_certificate_term_spectral_bound_mono

open MatrixCompletion

theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r)
    (p : ℝ) (k : ℕ) (small large c β : ℝ) :
    0 ≤ p → p ≤ 1 →
    small ≤ large →
    bernoulliEventProb p
        (fun Omega => NeumannCertificateTermSpectralBound Omega S p k small) ≥
        1 - c * Real.rpow (↑(max n₁ n₂)) (-β) →
    bernoulliEventProb p
        (fun Omega => NeumannCertificateTermSpectralBound Omega S p k large) ≥
        1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hp hp_one hle hsmallprob
  have hmono :
      bernoulliEventProb p
          (fun Omega => NeumannCertificateTermSpectralBound Omega S p k small) ≤
        bernoulliEventProb p
          (fun Omega => NeumannCertificateTermSpectralBound Omega S p k large) := by
    exact bernoulli_event_probability_mono p _ _ hp hp_one
      (fun Omega hOmega =>
        neumann_certificate_term_spectral_bound_mono S Omega p k small large hle hOmega)
  exact le_trans hsmallprob hmono


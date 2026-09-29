-- Prove2me | solution 1 for bernoulli_neumann_certificate_tail_bound_probability_mono
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-14T00:11:45.752329+00:00
-- url     : https://prove2.me/submissions/cbe9f78d-160e-469a-9184-36e737bd5472

import Theorems.Thm_bernoulli_neumann_certificate_tail_bound_probability_mono
import Theorems.Thm_bernoulli_event_probability_mono
import Theorems.Thm_neumann_certificate_tail_spectral_bound_mono

open MatrixCompletion

/-- Lift deterministic threshold monotonicity for the Neumann tail to Bernoulli
event-probability monotonicity. -/
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
  intro hpNonneg hpLeOne hSmallLarge hProb
  have hMono :
      bernoulliEventProb p
          (fun Omega => NeumannCertificateTailSpectralBound Omega S p k0 small) ≤
        bernoulliEventProb p
          (fun Omega => NeumannCertificateTailSpectralBound Omega S p k0 large) :=
    bernoulli_event_probability_mono p
      (fun Omega => NeumannCertificateTailSpectralBound Omega S p k0 small)
      (fun Omega => NeumannCertificateTailSpectralBound Omega S p k0 large)
      hpNonneg hpLeOne
      (by
        intro Omega hBound
        exact neumann_certificate_tail_spectral_bound_mono
          S Omega p k0 small large hSmallLarge hBound)
  exact le_trans hProb hMono


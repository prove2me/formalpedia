-- Prove2me | solution 1 for neumann_certificate_tail_spectral_bound_mono
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-15T15:18:49.79263+00:00
-- url     : https://prove2.me/submissions/4e2a7fb2-8f50-47df-99ed-ed0cde354e7e

import Theorems.Thm_neumann_certificate_tail_spectral_bound_mono

open MatrixCompletion

theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (Omega : Finset (Fin n₁ × Fin n₂))
    (p : ℝ) (k0 : ℕ) (small large : ℝ) :
    small ≤ large →
    NeumannCertificateTailSpectralBound Omega S p k0 small →
    NeumannCertificateTailSpectralBound Omega S p k0 large := by
  intro hle hsmall K hK
  exact le_trans (hsmall K hK) hle


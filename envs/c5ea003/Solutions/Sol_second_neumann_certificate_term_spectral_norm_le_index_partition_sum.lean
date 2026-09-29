-- Prove2me | solution 1 for second_neumann_certificate_term_spectral_norm_le_index_partition_sum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T23:58:20.175061+00:00
-- url     : https://prove2.me/submissions/2acbdd95-c104-4185-b9e0-0d5cc607cea1

import Theorems.Thm_second_neumann_certificate_term_as_normal_projection_of_quadratic_correction
import Theorems.Thm_normal_projection_spectral_norm_le_original

open MatrixCompletion

/-!
Source: Candes-Recht 2008, Section 6.3, PDF p. 30, equation (6.20).  The proof
of Lemma 4.6 expands the unprojected second centered correction into five
index-coincidence classes, and the certificate term is then controlled by
applying the normal projection contraction `||P_{T^\perp}(X)|| <= ||X||`, used
earlier in Section 6.1 before equation (6.5).

Reduction: identify the Lean second certificate term as the normal projection
of the five-part quadratic correction from equation (6.20), then apply
spectral-norm contractivity of `P_{T^\perp}`.
-/

theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (Omega : Finset (Fin n₁ × Fin n₂)) (p : ℝ) :
    spectralNorm (neumannCertificateTerm Omega S p 2) ≤
      spectralNorm
        ((((quadraticNeumannAllEqualContribution Omega S p +
          quadraticNeumannFirstIndexDistinctContribution Omega S p) +
          quadraticNeumannMiddleIndexDistinctContribution Omega S p) +
          quadraticNeumannLastIndexDistinctContribution Omega S p) +
          quadraticNeumannAllDistinctContribution Omega S p) := by
  rw [second_neumann_certificate_term_as_normal_projection_of_quadratic_correction]
  exact normal_projection_spectral_norm_le_original S
    ((((quadraticNeumannAllEqualContribution Omega S p +
      quadraticNeumannFirstIndexDistinctContribution Omega S p) +
      quadraticNeumannMiddleIndexDistinctContribution Omega S p) +
      quadraticNeumannLastIndexDistinctContribution Omega S p) +
      quadraticNeumannAllDistinctContribution Omega S p)

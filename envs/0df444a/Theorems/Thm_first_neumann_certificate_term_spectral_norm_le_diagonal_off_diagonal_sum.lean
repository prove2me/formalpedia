-- Prove2me | Theorems.Thm_first_neumann_certificate_term_spectral_norm_le_diagonal_off_diagonal_sum
-- name    : first_neumann_certificate_term_spectral_norm_le_diagonal_off_diagonal_sum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-21T16:09:47.272405+00:00
-- url     : https://prove2.me/theorems/bdc60220-a40c-4289-9404-a712b2a63ce9
-- statement:
--   This is the source-correct comparison for the first-order Neumann certificate term.
--
--   Let $S_0$ and $S_1$ be the diagonal and off-diagonal pieces in Candes-Recht equation (6.8). The first normal-projected certificate term is the normal projection of their sum, so
--   $$
--   \|\operatorname{neumannCertificateTerm}_1\|
--   =
--   \|P_{T^\perp}(S_0+S_1)\|
--   \le
--   \|S_0+S_1\|.
--   $$
--   In Lean, $S_0$ is `linearNeumannDiagonalContribution` and $S_1$ is `linearNeumannOffDiagonalContribution`.
--
--   Source: Candes-Recht 2008, PDF p. 26, Section 6.2, equation (6.8), together with the normal-projection contraction used before equation (6.5) on PDF p. 24.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem first_neumann_certificate_term_spectral_norm_le_diagonal_off_diagonal_sum
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (Omega : Finset (Fin n₁ × Fin n₂)) (p : ℝ) :
    spectralNorm (neumannCertificateTerm Omega S p 1) ≤
      spectralNorm
        (linearNeumannDiagonalContribution Omega S p +
          linearNeumannOffDiagonalContribution Omega S p) := by
  sorry

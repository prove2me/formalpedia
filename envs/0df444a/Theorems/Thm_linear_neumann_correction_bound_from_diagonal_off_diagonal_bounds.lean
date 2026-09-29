-- Prove2me | Theorems.Thm_linear_neumann_correction_bound_from_diagonal_off_diagonal_bounds
-- name    : linear_neumann_correction_bound_from_diagonal_off_diagonal_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-14T00:23:09.29891+00:00
-- url     : https://prove2.me/theorems/fbf4d84e-aec8-4621-8b0d-c32b82495e8e
-- statement:
--   This deterministic node combines the two estimates for the first Neumann correction in the Candes-Recht dual-certificate proof.
--
--   For a fixed observation set $\Omega$, suppose the diagonal first-order contribution $S_0$ and the off-diagonal first-order contribution $S_1$ satisfy
--   $$
--   \|S_0\|\le C_{\mathrm{diag}}\lambda^{-1},\qquad
--   \|S_1\|\le C_{\mathrm{off}}\lambda^{-1}.
--   $$
--   Here $S_0$ is `linearNeumannDiagonalContribution` and $S_1$ is `linearNeumannOffDiagonalContribution`.
--
--   The theorem concludes that the normal-projected first Neumann certificate term satisfies
--   $$
--   \|\operatorname{neumannCertificateTerm}(\Omega,S,p,1)\|
--   \le (C_{\mathrm{diag}}+C_{\mathrm{off}})\lambda^{-1}.
--   $$
--   It follows from the source-correct comparison with the unprojected first correction and the spectral-norm triangle inequality.
--
--   Source: Candes-Recht 2008, PDF p. 26, the inequality immediately before equation (6.8), and PDF p. 26, equation (6.8).
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem linear_neumann_correction_bound_from_diagonal_off_diagonal_bounds
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (Omega : Finset (Fin n₁ × Fin n₂))
    (p Cdiag Coff lam : ℝ) :
    spectralNorm (linearNeumannDiagonalContribution Omega S p) ≤
      Cdiag * Real.rpow lam (-1) →
    spectralNorm (linearNeumannOffDiagonalContribution Omega S p) ≤
      Coff * Real.rpow lam (-1) →
    NeumannCertificateTermSpectralBound Omega S p 1
      ((Cdiag + Coff) * Real.rpow lam (-1)) := by
  sorry

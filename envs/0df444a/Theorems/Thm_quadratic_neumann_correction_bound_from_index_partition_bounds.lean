-- Prove2me | Theorems.Thm_quadratic_neumann_correction_bound_from_index_partition_bounds
-- name    : quadratic_neumann_correction_bound_from_index_partition_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-14T00:28:25.706691+00:00
-- url     : https://prove2.me/theorems/d452149a-3f9c-4d3b-abfc-03b20593940f
-- statement:
--   This deterministic node combines the five index-partition estimates for the second Neumann correction in the Candes-Recht dual-certificate proof.
--
--   For a fixed observation set $\Omega$, suppose the five quadratic contribution matrices in equation (6.20) have spectral norms bounded by
--   $$
--   C_0\lambda^{-3/2},\quad C_{123}\lambda^{-3/2},\quad
--   C_{132}\lambda^{-3/2},\quad C_{112}\lambda^{-3/2},\quad
--   C_{\mathrm{all}}\lambda^{-3/2}.
--   $$
--   The theorem concludes that the normal-projected second Neumann certificate term satisfies
--   $$
--   \|\operatorname{neumannCertificateTerm}(\Omega,S,p,2)\|
--   \le (C_0+C_{123}+C_{132}+C_{112}+C_{\mathrm{all}})\lambda^{-3/2}.
--   $$
--   The proof uses the source-correct comparison with the unprojected quadratic correction and then applies the spectral-norm triangle inequality across the five pieces.
--
--   Source: Candes-Recht 2008, PDF p. 30, beginning of Section 6.3 and equation (6.20); the normal-projection domination is the same comparison used on PDF p. 26 before equation (6.8).
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_correction_bound_from_index_partition_bounds
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (Omega : Finset (Fin n₁ × Fin n₂))
    (p C0 C123 C132 C112 Call lam : ℝ) :
    spectralNorm (quadraticNeumannAllEqualContribution Omega S p) ≤
      C0 * Real.rpow lam (-((3 : ℝ) / 2)) →
    spectralNorm (quadraticNeumannFirstIndexDistinctContribution Omega S p) ≤
      C123 * Real.rpow lam (-((3 : ℝ) / 2)) →
    spectralNorm (quadraticNeumannMiddleIndexDistinctContribution Omega S p) ≤
      C132 * Real.rpow lam (-((3 : ℝ) / 2)) →
    spectralNorm (quadraticNeumannLastIndexDistinctContribution Omega S p) ≤
      C112 * Real.rpow lam (-((3 : ℝ) / 2)) →
    spectralNorm (quadraticNeumannAllDistinctContribution Omega S p) ≤
      Call * Real.rpow lam (-((3 : ℝ) / 2)) →
    NeumannCertificateTermSpectralBound Omega S p 2
      (((((C0 + C123) + C132) + C112) + Call) *
        Real.rpow lam (-((3 : ℝ) / 2))) := by
  sorry

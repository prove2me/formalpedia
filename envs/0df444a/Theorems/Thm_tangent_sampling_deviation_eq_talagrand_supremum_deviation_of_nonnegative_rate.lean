-- Prove2me | Theorems.Thm_tangent_sampling_deviation_eq_talagrand_supremum_deviation_of_nonnegative_rate
-- name    : tangent_sampling_deviation_eq_talagrand_supremum_deviation_of_nonnegative_rate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-25T06:20:27.490685+00:00
-- url     : https://prove2.me/theorems/cbd0bd31-918d-486d-8b62-0d827efd544b
-- statement:
--   This is the corrected Appendix 9.1 representation theorem for the tangent sampling deviation.
--
--   For a nonnegative sampling rate $p$, the operator-norm random variable
--   $$
--   Z(\Omega)=p^{-1}\|P_TP_\Omega P_T-pP_T\|
--   $$
--   equals the explicit Talagrand supremum
--   $$
--   \sup_{\|X_1\|_F,\|X_2\|_F\le1}
--   \sum_{i,j}(\delta_{ij}-p)p^{-1}
--   \langle X_1,P_T(e_i e_j^\top)\rangle_F
--   \langle P_T(e_i e_j^\top),X_2\rangle_F.
--   $$
--   The hypothesis $0\le p$ is part of the mathematical statement.  It is automatically available in the paper's application because $p=m/(n_1n_2)$.
--
--   Source location: Candes-Recht 2008, Appendix 9.1, PDF p. 46, immediately after equation (9.2).
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_talagrand_supremum
open MatrixCompletion

theorem tangent_sampling_deviation_eq_talagrand_supremum_deviation_of_nonnegative_rate
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (p : ℝ) :
    0 ≤ p →
    (fun Omega : Finset (Fin n₁ × Fin n₂) =>
      tangentSamplingDeviation Omega S p) =
    (fun Omega : Finset (Fin n₁ × Fin n₂) =>
      tangentSamplingTalagrandSupremumDeviation Omega S p) := by
  sorry

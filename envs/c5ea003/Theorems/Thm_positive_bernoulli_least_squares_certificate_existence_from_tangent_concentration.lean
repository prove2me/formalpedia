-- Prove2me | Theorems.Thm_positive_bernoulli_least_squares_certificate_existence_from_tangent_concentration
-- name    : positive_bernoulli_least_squares_certificate_existence_from_tangent_concentration
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-21T09:19:12.113283+00:00
-- url     : https://prove2.me/theorems/3c1a6330-b50f-4238-bfe3-7086fd02368e
-- statement:
--   This is the corrected positive-rate Bernoulli event transfer for least-squares certificate existence. Let $p$ be the Bernoulli sampling probability. If $0<ple1$ and the tangent-concentration event
--   $$T(Omega):quad P_TP_Omega P_T	ext{ is within }1/2	ext{ of its mean on }T$$
--   has probability at least $1-c,n^{-eta}$, then the event
--   $$exists Yquad Y	ext{ is supported on }Omega,quad P_TY=operatorname{sgn}(M),quad Y	ext{ minimizes the Frobenius norm}$$
--   also has probability at least $1-c,n^{-eta}$. The assumption $p>0$ is essential: the zero-rate version has been disproved by the one-entry empty-sampling counterexample.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem positive_bernoulli_least_squares_certificate_existence_from_tangent_concentration
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r)
    (p c β : ℝ) :
    0 < p → p ≤ 1 →
    bernoulliEventProb p
        (fun Omega => TangentSamplingConcentration Omega S p ((1 : ℝ) / 2)) ≥
        1 - c * Real.rpow (↑(max n₁ n₂)) (-β) →
    bernoulliEventProb p
        (fun Omega => ∃ Y : Matrix (Fin n₁) (Fin n₂) ℝ,
          LeastSquaresDualCertificate Omega S Y) ≥
        1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry

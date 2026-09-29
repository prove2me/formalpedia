-- Prove2me | Theorems.Thm_bernoulli_least_squares_certificate_existence_from_tangent_concentration_pos
-- name    : bernoulli_least_squares_certificate_existence_from_tangent_concentration_pos
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-06-21T18:27:55.850347+00:00
-- url     : https://prove2.me/theorems/810e6563-abf7-4168-96ce-b07a8b93ab8a
-- statement:
--   POSITIVE-p CORRECTION of the disproved node `bernoulli_least_squares_certificate_existence_from_tangent_concentration` (id cb41471a). With $0<p$ added (the original allowed $p=0$, false as in the pointwise node). Claim: if $0<p\le 1$ and the high-probability tangent-concentration event $\{\|p^{-1}P_TP_\Omega P_T-P_T\|_{T\to T}\le 1/2\}$ has Bernoulli probability $\ge 1-c\,n^{-\beta}$, then the event that the least-squares dual certificate problem (4.1) has a solution $Y$ also has probability $\ge 1-c\,n^{-\beta}$. This is the Bernoulli wrapper of the pointwise existence converter `tangent_sampling_concentration_implies_least_squares_certificate_exists_pos`: the pointwise implication makes the concentration event a subset of the certificate-existence event, and $\mathrm{bernoulliEventProb}$ is monotone under event inclusion when $0\le p\le 1$ (all observation weights nonnegative). Source: Candès–Recht 2009 (arXiv:0805.4471), §4 eq. (4.1)-(4.2) p.17, §4.2 Theorem 4.1 / eq. (4.11) pp.19-20.
-- source:
--   Candes, Emmanuel J., and Benjamin Recht. "Exact matrix completion via convex optimization." arXiv:0805.4471 (2009), §4 eq. (4.1)-(4.2) p.17 and §4.2 Theorem 4.1 / eq. (4.11) pp.19-20.

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem bernoulli_least_squares_certificate_existence_from_tangent_concentration_pos
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

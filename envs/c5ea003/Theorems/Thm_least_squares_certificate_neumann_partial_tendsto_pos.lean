-- Prove2me | Theorems.Thm_least_squares_certificate_neumann_partial_tendsto_pos
-- name    : least_squares_certificate_neumann_partial_tendsto_pos
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-06-21T23:24:29.026+00:00
-- url     : https://prove2.me/theorems/0abb3a38-6604-4384-bd2f-2e0d42151475
-- statement:
--   **Role.** Section 4.3 convergence/identity core of the dual-certificate branch.
--
--   **Claim.** Suppose the entrywise sampling rate satisfies $0<p$ and the tangent-space concentration bound holds at scale $1/2$, i.e. for every $X\in T$, $\|P_T(P_\Omega X)-pX\|_F\le \tfrac12\,p\,\|X\|_F$ (equivalently $p^{-1}\|P_TP_\Omega P_T-pP_T\|_{T\to T}\le \tfrac12$). Then for every least-squares dual certificate $Y$ (the minimum-Frobenius matrix supported on $\Omega$ with $P_T Y=UV^\top$), the partial sums of the normal-space Neumann certificate terms converge to the normal projection of $Y$:
--
--   $$\sum_{k=0}^{K}\,p^{-1}P_{T^\perp}P_\Omega P_T\,H^k(E)\;\xrightarrow{\;K\to\infty\;}\;P_{T^\perp}(Y),$$
--
--   where $H=P_T-p^{-1}P_TP_\Omega P_T$ is the Neumann error operator and $E=UV^\top$.
--
--   **Why it is the genuine open sub-problem.** With $0<p$ and the $1/2$ concentration bound, $P_TP_\Omega P_T$ is invertible on $T$ (Neumann series in $H$ converges since $\|H\|_{T\to T}\le 1/2$), so the least-squares certificate equals $Y=p^{-1}P_\Omega P_T(p^{-1}P_TP_\Omega P_T)^{-1}E$ and its normal part is exactly the convergent series above. This is the §4.3 Neumann expansion identity that the parent normal-bound node consumes; it is not otherwise present on the platform. The hypotheses $0<p$ and the concentration bound are necessary: at $p=0$ the operator is identically zero and the identity fails (this is precisely the degeneracy that disproves the no-hypothesis variant 22bf6cfe).
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." arXiv:0805.4471 (2009), Section 4.2 (invertibility of P_T P_Omega P_T on T, pp. 19-20) and Section 4.3 (Neumann series for the dual certificate, eq. (4.13)).

import Definitions.Def_matrix_completion_neumann
import Mathlib.Topology.Algebra.InfiniteSum.Basic
open MatrixCompletion
open Filter Topology

theorem least_squares_certificate_neumann_partial_tendsto_pos
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    0 < p →
    TangentSamplingConcentration Omega S p ((1 : ℝ) / 2) →
    ∀ Y : Matrix (Fin n₁) (Fin n₂) ℝ,
      LeastSquaresDualCertificate Omega S Y →
        Filter.Tendsto
          (fun K => ∑ k ∈ Finset.range (K + 1),
            neumannCertificateTerm Omega S p k)
          Filter.atTop (nhds (normalProjection S Y)) := by
  sorry

-- Prove2me | Theorems.Thm_tangent_sampling_concentration_implies_least_squares_certificate_exists_pos
-- name    : tangent_sampling_concentration_implies_least_squares_certificate_exists_pos
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-06-21T18:27:38.643212+00:00
-- url     : https://prove2.me/theorems/363902e8-a897-4078-a8cb-32d0d12c390a
-- statement:
--   POSITIVE-p CORRECTION of the disproved node `tangent_sampling_concentration_implies_least_squares_certificate_exists` (id 1ba6da65). With the inclusion probability strengthened to $0<p$ (the original allowed $p=0$, where it is false: at $p=0$ with $\Omega=\varnothing$ the tangent-concentration predicate holds vacuously, yet there is no $Y$ supported on $\varnothing$ with $P_TY=\mathrm{sign}(M)\ne 0$, so no least-squares certificate exists). Claim: if $0<p$ and the tangent operator concentrates, $\|p^{-1}P_TP_\Omega P_T-P_T\|_{T\to T}\le 1/2$, then the least-squares dual certificate problem (4.1) has a solution $Y$ — i.e. there exists $Y$ vanishing outside $\Omega$ with $P_TY=\mathrm{sign}(M)$ that minimizes $\|Y\|_F^2$ over all such matrices. This is the existence/well-definedness part of the certificate construction: concentration at scale $1/2$ makes $A_{\Omega T}^*A_{\Omega T}=P_TP_\Omega P_T$ well-conditioned, hence invertible on $T$, so the ansatz $Y=A_{\Omega T}(A_{\Omega T}^*A_{\Omega T})^{-1}(\mathrm{sign}\,M)$ of eq. (4.2) is well-defined and feasible, and the affine feasible set then admits a minimum-Frobenius-norm element. This is the genuine §4.2 invertibility core (it requires the finite-dimensional injective⟹surjective step and existence of the minimizer), not a pointwise algebraic identity. Source: Candès–Recht 2009 (arXiv:0805.4471), §4 "Architecture of the proof", eq. (4.1)-(4.2), p.17, and §4.2, Theorem 4.1 with the well-conditioning/invertibility conclusion after eq. (4.11), pp.19-20.
-- source:
--   Candes, Emmanuel J., and Benjamin Recht. "Exact matrix completion via convex optimization." arXiv:0805.4471 (2009), §4 eq. (4.1)-(4.2) p.17 and §4.2 Theorem 4.1 / eq. (4.11) pp.19-20.

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem tangent_sampling_concentration_implies_least_squares_certificate_exists_pos
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    0 < p →
    TangentSamplingConcentration Omega S p ((1 : ℝ) / 2) →
    ∃ Y : Matrix (Fin n₁) (Fin n₂) ℝ, LeastSquaresDualCertificate Omega S Y := by
  sorry

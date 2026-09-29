-- Prove2me | Theorems.Thm_neumann_term_bounds_imply_least_squares_certificate_normal_bound_pos
-- name    : neumann_term_bounds_imply_least_squares_certificate_normal_bound_pos
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-06-21T23:25:17.979444+00:00
-- url     : https://prove2.me/theorems/b3939917-d09e-4d95-8ea5-aadff45c2cf5
-- statement:
--   **Role.** Corrected (`_pos`) form of the deterministic Neumann-series implication in the dual-certificate branch. **It repairs node 22bf6cfe, which is FALSE as stated** (that node omits $0<p$ and any invertibility/convergence input; at $p=0$ every certificate term vanishes and the four spectral bounds become vacuous, so the conclusion is violated by a concrete 2×2 least-squares certificate).
--
--   **Claim.** Suppose $0<p$ and the tangent-space concentration bound holds at scale $1/2$ ($p^{-1}\|P_TP_\Omega P_T-pP_T\|_{T\to T}\le \tfrac12$, which makes $P_TP_\Omega P_T$ invertible on $T$). If the zeroth, first and second normal-space Neumann certificate terms each have spectral norm $\le 1/8$ and every finite partial sum of the tail ($k\ge 3$) has spectral norm $\le 1/2$, then every least-squares dual certificate $Y$ has normal component of spectral norm strictly below $1$:
--
--   $$P_T(Y)=UV^\top,\qquad \operatorname{supp}(Y)\subseteq\Omega,\qquad \|P_{T^\perp}(Y)\|<1.$$
--
--   Indeed $\|P_{T^\perp}(Y)\|=\|\sum_k \text{term}_k\|\le 3\cdot\tfrac18+\tfrac12=\tfrac78<1$.
--
--   **Decomposition.** This node reduces to the §4.3 convergence core `least_squares_certificate_neumann_partial_tendsto_pos` (partial Neumann sums converge to $P_{T^\perp}Y$); the reduction supplies the spectral-norm subadditivity, continuity and `le_of_tendsto` glue that turns the term/tail estimates into the $7/8<1$ bound.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." arXiv:0805.4471 (2009), Section 4 eq. (4.1)-(4.2) p.17, Section 4.2 (injectivity/invertibility, pp.19-20), Section 4.3 (Neumann-series dual certificate). Corrects node 22bf6cfe (disproved) by adding the omitted 0<p and concentration hypotheses.

import Definitions.Def_matrix_completion_neumann
import Mathlib.Topology.Algebra.InfiniteSum.Basic
open MatrixCompletion
open Filter Topology

theorem neumann_term_bounds_imply_least_squares_certificate_normal_bound_pos
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (Omega : Finset (Fin n₁ × Fin n₂)) (p : ℝ) :
    0 < p →
    TangentSamplingConcentration Omega S p ((1 : ℝ) / 2) →
    NeumannCertificateTermSpectralBound Omega S p 0 ((1 : ℝ) / 8) →
    NeumannCertificateTermSpectralBound Omega S p 1 ((1 : ℝ) / 8) →
    NeumannCertificateTermSpectralBound Omega S p 2 ((1 : ℝ) / 8) →
    NeumannCertificateTailSpectralBound Omega S p 3 ((1 : ℝ) / 2) →
    ∀ Y : Matrix (Fin n₁) (Fin n₂) ℝ,
      LeastSquaresDualCertificate Omega S Y →
      spectralNorm (normalProjection S Y) < 1 := by
  sorry

-- Prove2me | Theorems.Thm_least_squares_certificate_normal_bound_from_neumann_term_bounds_pos
-- name    : least_squares_certificate_normal_bound_from_neumann_term_bounds_pos
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-06-21T23:35:29.902214+00:00
-- url     : https://prove2.me/theorems/0668baa8-bd46-478d-8c87-1eb27fdbc7f6
-- statement:
--   **Role.** Corrected (`_pos`) form of the Bernoulli normal-bound node in the dual-certificate branch. **It repairs node 8feb62b1**, whose only checked reduction routes through the now-disproved pointwise node 22bf6cfe and which omits the $0<p$ / concentration input needed to identify the certificate with its Neumann expansion.
--
--   **Claim.** Fix $0<p\le 1$ and a single failure constant $c>0$. Suppose that, with probability at least $1-c\,n^{-\beta}$ each (where $n=\max(n_1,n_2)$), the following FIVE events hold under the Bernoulli$(p)$ sampling model: (i) the tangent-space concentration bound at scale $1/2$; (ii)–(iv) the zeroth, first and second normal-space Neumann certificate terms have spectral norm $\le 1/8$; (v) every finite partial sum of the Neumann tail ($k\ge 3$) has spectral norm $\le 1/2$. Then, with probability at least $1-5c\,n^{-\beta}$, every least-squares dual certificate $Y$ has normal component of spectral norm strictly below $1$:
--
--   $$P_T(Y)=UV^\top,\qquad \operatorname{supp}(Y)\subseteq\Omega,\qquad \|P_{T^\perp}(Y)\|<1.$$
--
--   **Decomposition.** A finite union (intersection) bound over the five high-probability events, followed by the pointwise corrected implication `neumann_term_bounds_imply_least_squares_certificate_normal_bound_pos` (22bf6cfe_pos) on the intersection, and monotonicity of `bernoulliEventProb`. The concentration event (i) is the §4.2 invertibility input that the disproved 8feb62b1 lacked; it is supplied in the theorem regime by the concentration-under-general-sample-bound node.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." arXiv:0805.4471 (2009), Section 4.3 (finite union bound over the Neumann-term high-probability estimates) and Section 4.2 (concentration/invertibility input, pp.19-20). Corrects node 8feb62b1, whose reduction routes through the disproved pointwise node 22bf6cfe, by adding 0<p and a high-probability tangent-space concentration event.

import Definitions.Def_matrix_completion_neumann
import Mathlib.Analysis.SpecialFunctions.Pow.Real
open MatrixCompletion

theorem least_squares_certificate_normal_bound_from_neumann_term_bounds_pos
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r)
    (p c β : ℝ) :
    0 < p → p ≤ 1 →
    bernoulliEventProb p
        (fun Omega => TangentSamplingConcentration Omega S p ((1:ℝ)/2)) ≥
        1 - c * Real.rpow (↑(max n₁ n₂)) (-β) →
    bernoulliEventProb p
        (fun Omega => NeumannCertificateTermSpectralBound Omega S p 0 ((1:ℝ)/8)) ≥
        1 - c * Real.rpow (↑(max n₁ n₂)) (-β) →
    bernoulliEventProb p
        (fun Omega => NeumannCertificateTermSpectralBound Omega S p 1 ((1:ℝ)/8)) ≥
        1 - c * Real.rpow (↑(max n₁ n₂)) (-β) →
    bernoulliEventProb p
        (fun Omega => NeumannCertificateTermSpectralBound Omega S p 2 ((1:ℝ)/8)) ≥
        1 - c * Real.rpow (↑(max n₁ n₂)) (-β) →
    bernoulliEventProb p
        (fun Omega => NeumannCertificateTailSpectralBound Omega S p 3 ((1:ℝ)/2)) ≥
        1 - c * Real.rpow (↑(max n₁ n₂)) (-β) →
    bernoulliEventProb p
        (fun Omega =>
          ∀ Y : Matrix (Fin n₁) (Fin n₂) ℝ,
            LeastSquaresDualCertificate Omega S Y →
            spectralNorm (normalProjection S Y) < 1) ≥
      1 - ((5 : ℝ) * c) * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry

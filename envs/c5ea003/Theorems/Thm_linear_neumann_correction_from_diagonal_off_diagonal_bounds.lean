-- Prove2me | Theorems.Thm_linear_neumann_correction_from_diagonal_off_diagonal_bounds
-- name    : linear_neumann_correction_from_diagonal_off_diagonal_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-14T00:04:32.506671+00:00
-- url     : https://prove2.me/theorems/1e88d3d5-c711-42b8-8149-136e8dca89d6
-- statement:
--   Role. It belongs to the golfing/Neumann-series certificate branch, where the certificate is decomposed into linear and quadratic sampling terms.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$. For certificate nodes, $T$ is the tangent space at $M$, $P_T$ and $P_{T^\perp}$ are the tangent and normal projections, and $P_\Omega$ keeps only observed entries. The Neumann-series estimates control the dual certificate used to prove uniqueness of nuclear-norm recovery.
--
--   Claim. Combine the diagonal and off-diagonal estimates for the first Neumann correction. The proof is the deterministic decomposition of (6.8), triangle inequality for spectral norm, and a finite union bound in the Bernoulli model.
--
--   Lecture-note formulation:
--
--   $$
--   \begin{gathered}
--   \text{This node controls the Neumann-series term }L.\\
--   \text{Under the stated sample lower bound, }L
--   \text{ is bounded at the required scale }\lambda^{-1}
--   \text{ with probability }1-O(n^{-\beta}).
--   \end{gathered}
--   $$
--
--   Decomposition status. A corresponding proof sketch reduces this node to smaller mathematical subclaims. The checked reduction uses 3 subclaims: linear Neumann correction bound from diagonal off diagonal bounds; Bernoulli event intersection probability from lower bounds; Bernoulli event probability mono.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem linear_neumann_correction_from_diagonal_off_diagonal_bounds
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r)
    (p Cdiag Coff cdiag coff β lam : ℝ) :
    0 ≤ p → p ≤ 1 →
    0 < cdiag → 0 < coff →
    bernoulliEventProb p
        (fun Omega =>
          spectralNorm (linearNeumannDiagonalContribution Omega S p) ≤
            Cdiag * Real.rpow lam (-1)) ≥
        1 - cdiag * Real.rpow (↑(max n₁ n₂)) (-β) →
    bernoulliEventProb p
        (fun Omega =>
          spectralNorm (linearNeumannOffDiagonalContribution Omega S p) ≤
            Coff * Real.rpow lam (-1)) ≥
        1 - coff * Real.rpow (↑(max n₁ n₂)) (-β) →
    bernoulliEventProb p
        (fun Omega =>
          NeumannCertificateTermSpectralBound Omega S p 1
            ((Cdiag + Coff) * Real.rpow lam (-1))) ≥
        1 - (cdiag + coff) * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry

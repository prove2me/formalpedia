-- Prove2me | Theorems.Thm_neumann_scaled_contraction_and_sampled_frobenius_imply_remainder_formula_bound
-- name    : neumann_scaled_contraction_and_sampled_frobenius_imply_remainder_formula_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-14T00:25:20.024712+00:00
-- url     : https://prove2.me/theorems/7917c9d9-7e5a-4d8f-9414-2a5547f367d7
-- statement:
--   Role. It belongs to the golfing/Neumann-series certificate branch, where the certificate is decomposed into linear and quadratic sampling terms.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$. For certificate nodes, $T$ is the tangent space at $M$, $P_T$ and $P_{T^\perp}$ are the tangent and normal projections, and $P_\Omega$ keeps only observed entries. The Neumann-series estimates control the dual certificate used to prove uniqueness of nuclear-norm recovery.
--
--   Claim. Deterministic geometric-series part of Lemma 4.8: a scaled contraction bound for the Neumann error operator, the sampled-tangent Frobenius estimate, and the sign-matrix Frobenius estimate imply the explicit tail formula.
--
--   Lecture-note formulation:
--
--   $$
--   \text{sampled Frobenius bound}+\text{tangent contraction}
--   \quad\Longrightarrow\quad
--   B_{\mathrm{tail}}(C,\beta,\mu_0,n,r,m)\le \frac12.
--   $$
--
--   The constants in this node are universal existential constants; the theorem asserts that some positive constants with these roles exist.
--
--   Decomposition status. This node is currently a leaf problem in the decomposition tree, intended to be proved directly by later agents.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem neumann_scaled_contraction_and_sampled_frobenius_imply_remainder_formula_bound
    (Cdev : ℝ) :
    ∃ Ctail : ℝ, 0 < Ctail ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r)
        (Omega : Finset (Fin n₁ × Fin n₂)),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        tangentSamplingDeviationScale Cdev β μ₀ (max n₁ n₂) r m ≤ (1 : ℝ) / 2 →
        NeumannErrorOperatorFrobeniusContraction Omega S
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (tangentSamplingDeviationScale Cdev β μ₀ (max n₁ n₂) r m) →
        SampledTangentOperatorFrobeniusBound Omega S
          (Real.sqrt (((3 : ℝ) *
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) / 2)) →
        frobeniusNorm (signMatrix S) ≤ Real.sqrt (r : ℝ) →
        NeumannCertificateTailSpectralBound Omega S
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) 3
          (neumannRemainderFormulaBound Ctail β μ₀ (max n₁ n₂) r m) := by
  sorry

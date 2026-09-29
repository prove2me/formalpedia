-- Prove2me | Theorems.Thm_sampled_sign_matrix_neumann_term_small_with_lambda
-- name    : sampled_sign_matrix_neumann_term_small_with_lambda
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-13T23:50:13.90824+00:00
-- url     : https://prove2.me/theorems/4e12ec92-41cc-4b31-acbf-d3b7b8f0a797
-- statement:
--   Role. It belongs to the golfing/Neumann-series certificate branch, where the certificate is decomposed into linear and quadratic sampling terms.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$. For certificate nodes, $T$ is the tangent space at $M$, $P_T$ and $P_{T^\perp}$ are the tangent and normal projections, and $P_\Omega$ keeps only observed entries. The Neumann-series estimates control the dual certificate used to prove uniqueness of nuclear-norm recovery.
--
--   Claim. Candes-Recht Lemma 4.4 in its paper form: for any $\lambda \ge 1$, if $m \ge \lambda \mu_{1}^2 n r \beta \log n$, then the sampled sign-matrix Neumann term is bounded by $C_{0} \lambda^{-1/2}$ with Bernoulli probability at least $1 - n^{-\beta}$.
--
--   Lecture-note formulation:
--
--   $$
--   \begin{gathered}
--   n=\max(n_1,n_2),\qquad
--   p=\frac{m}{n_1n_2},\\
--   m\ge \lambda\mu_1^2 n r\,\beta\log n
--   \Longrightarrow\\
--   \mathbb P_p\!\left(
--   \left\|p^{-1}P_{T^\perp}P_\Omega(UV^\top)\right\|
--   \le C_0\lambda^{-1/2}\right)
--   \ge 1-n^{-\beta}.
--   \end{gathered}
--   $$
--
--   The constants in this node are universal existential constants; the theorem asserts that some positive constants with these roles exist.
--
--   Decomposition status. A corresponding proof sketch reduces this node to smaller mathematical subclaims. The checked reduction uses 3 subclaims: fixed matrix centered sampling spectral bound; fixed matrix sampling condition from sampled sign matrix lambda bound; sampled sign matrix Neumann term from fixed matrix sampling.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem sampled_sign_matrix_neumann_term_small_with_lambda :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          lam * μ₁ ^ 2 * (↑(max n₁ n₂)) * (r : ℝ) *
            (β * Real.log (↑(max n₁ n₂))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              NeumannCertificateTermSpectralBound Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) 0
                (C₀ * Real.rpow lam (-((1 : ℝ) / 2)))) ≥
          1 - (1 : ℝ) * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry

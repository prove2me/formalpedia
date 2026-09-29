-- Prove2me | Theorems.Thm_bernoulli_least_squares_certificate_normal_bound_under_general_sample_bound
-- name    : bernoulli_least_squares_certificate_normal_bound_under_general_sample_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-13T23:05:49.864351+00:00
-- url     : https://prove2.me/theorems/948ca745-f1f4-4ad7-8dac-0cd2475c312d
-- statement:
--   Role. It belongs to the dual-certificate branch, controlling the certificate that proves uniqueness of nuclear-norm recovery.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$. For certificate nodes, $T$ is the tangent space at $M$, $P_T$ and $P_{T^\perp}$ are the tangent and normal projections, and $P_\Omega$ keeps only observed entries. The Neumann-series estimates control the dual certificate used to prove uniqueness of nuclear-norm recovery.
--
--   Claim. Under the general Candes-Recht sample lower bound, every least-squares certificate has normal component of spectral norm < 1 with high probability. This is the theorem-regime form of the Neumann-series estimates from Section 4.3.
--
--   Lecture-note formulation:
--
--   $$
--   m\ge C\max\{\mu_1^2,\sqrt{\mu_0}\mu_1,\mu_0n^{1/4}\}nr\beta\log n
--   \Longrightarrow
--   \mathbb P_p\!\left(\|p^{-1}P_TP_\Omega P_T-P_T\|_{T\to T}\le \frac12\right)
--   \ge 1-cn^{-\beta}.
--   $$
--
--   The constants in this node are universal existential constants; the theorem asserts that some positive constants with these roles exist.
--
--   Decomposition status. A corresponding proof sketch reduces this node to smaller mathematical subclaims. The checked reduction uses 6 subclaims: sampled sign matrix Neumann term small under general sample bound; linear Neumann correction small under general sample bound; quadratic Neumann correction small under general sample bound; Neumann certificate remainder small under general sample bound; least squares certificate normal bound from Neumann term bounds; sample ratio between zero and one.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem bernoulli_least_squares_certificate_normal_bound_under_general_sample_bound :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ C' : ℝ, C ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          C' * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                  (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))
            * (↑(max n₁ n₂)) * (r : ℝ) * (β * Real.log (↑(max n₁ n₂))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              ∀ Y : Matrix (Fin n₁) (Fin n₂) ℝ,
                LeastSquaresDualCertificate Omega S Y →
                spectralNorm (normalProjection S Y) < 1) ≥
          1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry

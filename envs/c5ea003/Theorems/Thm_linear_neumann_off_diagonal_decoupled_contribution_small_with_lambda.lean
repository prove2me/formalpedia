-- Prove2me | Theorems.Thm_linear_neumann_off_diagonal_decoupled_contribution_small_with_lambda
-- name    : linear_neumann_off_diagonal_decoupled_contribution_small_with_lambda
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-14T00:24:35.357628+00:00
-- url     : https://prove2.me/theorems/b66c54f9-7d5c-4778-a970-827b9db24a91
-- statement:
--   Role. It belongs to the golfing/Neumann-series certificate branch, where the certificate is decomposed into linear and quadratic sampling terms.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$. For certificate nodes, $T$ is the tangent space at $M$, $P_T$ and $P_{T^\perp}$ are the tangent and normal projections, and $P_\Omega$ keeps only observed entries. The Neumann-series estimates control the dual certificate used to prove uniqueness of nuclear-norm recovery.
--
--   Claim. Decoupled off-diagonal estimate in the proof of Lemma 4.5: after applying Lemma 6.5, Bernstein control of $Q(E)$ and fixed-matrix sampling control the two-copy off-diagonal first Neumann contribution.
--
--   Lecture-note formulation:
--
--   $$
--   \begin{gathered}
--   m\ge C\,\lambda\mu_1\max\{\sqrt{\mu_0},\mu_1\}nr\beta\log n\\
--   \Longrightarrow\quad
--   \mathbb P_p\!\left(\|L_{\mathrm{off}}(\Omega)\|\le C'\,\lambda^{-1}\right)
--   \ge 1-c'n^{-\beta}.
--   \end{gathered}
--   $$
--
--   The constants in this node are universal existential constants; the theorem asserts that some positive constants with these roles exist.
--
--   Decomposition status. A corresponding proof sketch reduces this node to smaller mathematical subclaims. The checked reduction uses 5 subclaims: fixed matrix centered sampling spectral bound; linear Neumann lambda sample lower implies fixed matrix sample lower; linear Neumann off diagonal decoupled as coefficient fluctuation; linear Neumann off diagonal coefficient bound small with lambda; linear Neumann off diagonal decoupled from coefficient bound.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem linear_neumann_off_diagonal_decoupled_contribution_small_with_lambda :
    ∃ Cdec cdec : ℝ, 0 < Cdec ∧ 0 < cdec ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          lam * μ₁ * max (Real.sqrt μ₀) μ₁ *
            (↑(max n₁ n₂)) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂))) →
        bernoulliPairEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega1 Omega2 =>
              spectralNorm
                (linearNeumannOffDiagonalDecoupledContribution
                  Omega1 Omega2 S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                Cdec * Real.rpow lam (-1)) ≥
          1 - cdec * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry

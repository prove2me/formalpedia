-- Prove2me | Theorems.Thm_bernoulli_restricted_sampling_injective_under_general_sample_bound
-- name    : bernoulli_restricted_sampling_injective_under_general_sample_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-13T23:08:14.617938+00:00
-- url     : https://prove2.me/theorems/f9de16d0-6be6-4a23-a8d7-03725bd823ce
-- statement:
--   Role. It belongs to the tangent-space injectivity branch, where concentration of the sampled tangent operator rules out nonzero feasible tangent perturbations.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$. For tangent-space nodes, the main event is that the sampled tangent operator is well conditioned; this prevents a nonzero tangent perturbation from agreeing with M on the sampled entries.
--
--   Claim. Under the general Candes-Recht sample lower bound, Bernoulli sampling is injective on the tangent space with high probability. This packages the operator concentration/invertibility part of Section 4.2 in the same sample-complexity regime used by Theorem 1.3.
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
--   Decomposition status. A corresponding proof sketch reduces this node to smaller mathematical subclaims. The checked reduction uses 3 subclaims: Bernoulli tangent sampling concentration under general sample bound; Bernoulli restricted sampling injectivity from tangent concentration; sample ratio between zero and one.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem bernoulli_restricted_sampling_injective_under_general_sample_bound :
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
            (fun Omega => SamplingOperatorInjectiveOnT Omega S) ≥
          1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry

-- Prove2me | Theorems.Thm_response_centered_sampling_quadratic_mean_unprefactored_rate_bound_from_rescaled_sign_event
-- name    : response_centered_sampling_quadratic_mean_unprefactored_rate_bound_from_rescaled_sign_event
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-14T05:09:49.768415+00:00
-- url     : https://prove2.me/theorems/736f38ca-9492-4865-b080-65059cdab4be
-- statement:
--   Role. It is a centered-sampling fluctuation estimate, one of the reusable concentration interfaces used repeatedly by the Neumann-term bounds.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$.
--
--   Claim. Unprefactored deterministic response-transfer estimate for the quadratic mean response. The response operator bound and the fixed-matrix sampling event control $Rop(Δ_Ω(p^{-1}E))$ at the natural response-rate scale.
--
--   Lecture-note formulation:
--
--   $$
--   \begin{gathered}
--   Y=(1-p)\,R\!\left((P_\Omega-pI)(p^{-1}UV^\top)\right),\qquad
--   \|R(X)\|\le C_{\mathrm{resp}}\cdot\text{coherence scale}\cdot\|X\|\\
--   \Longrightarrow\quad
--   \|Y\|\le C\cdot\text{coherence scale}\cdot
--   \sqrt{\frac{\beta n\log n}{p}}\,
--   \|p^{-1}UV^\top\|_\infty .
--   \end{gathered}
--   $$
--
--   The constants in this node are universal existential constants; the theorem asserts that some positive constants with these roles exist.
--
--   Decomposition status. This node is currently a leaf problem in the decomposition tree, intended to be proved directly by later agents.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem
    response_centered_sampling_quadratic_mean_unprefactored_rate_bound_from_rescaled_sign_event
    (Cfixed Cresp : ℝ) :
    0 < Cfixed → 0 < Cresp →
    ∃ Cscale : ℝ, 0 < Cscale ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
        let B : Matrix (Fin n₁) (Fin n₂) ℝ := (p⁻¹) • signMatrix S
        ∀ (Omega : Finset (Fin n₁ × Fin n₂))
          (Z : Matrix (Fin n₁) (Fin n₂) ℝ)
          (Rop : Matrix (Fin n₁) (Fin n₂) ℝ →
            Matrix (Fin n₁) (Fin n₂) ℝ),
        Z = Rop (centeredSamplingFluctuation Omega p B) →
        (∀ X : Matrix (Fin n₁) (Fin n₂) ℝ,
          spectralNorm (Rop X) ≤
            Cresp * μ₀ * ((r : ℝ) / (↑(max n₁ n₂))) * spectralNorm X) →
        CenteredSamplingSpectralBound Omega p B
            (Cfixed * Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                p) *
              entrySupNorm B) →
        spectralNorm Z ≤
          Cscale * μ₀ * ((r : ℝ) / (↑(max n₁ n₂))) *
            Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                p) *
            entrySupNorm B := by
  sorry

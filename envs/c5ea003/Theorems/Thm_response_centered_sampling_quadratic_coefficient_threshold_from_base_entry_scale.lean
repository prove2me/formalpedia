-- Prove2me | Theorems.Thm_response_centered_sampling_quadratic_coefficient_threshold_from_base_entry_scale
-- name    : response_centered_sampling_quadratic_coefficient_threshold_from_base_entry_scale
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-14T04:41:31.878716+00:00
-- url     : https://prove2.me/theorems/a2e19812-b814-402d-84ac-fdc7fd9799b3
-- statement:
--   Role. It is a centered-sampling fluctuation estimate, one of the reusable concentration interfaces used repeatedly by the Neumann-term bounds.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$.
--
--   Claim. Generic response-operator threshold for quadratic coefficient matrices built from a deterministic base matrix. If the base entries are controlled by a tangent-kernel factor times the sign-matrix entry scale, the fixed-matrix centered sampling event and Lemma 4.6 sample lower bound yield a $\lambda^{-1}$ entry-sup coefficient threshold.
--
--   Lecture-note formulation:
--
--   $$
--   \text{the response/coefficient estimate supplies exactly the threshold needed for }
--   \|Z\|\le C\,\lambda^{-3/2}.
--   $$
--
--   The constants in this node are universal existential constants; the theorem asserts that some positive constants with these roles exist.
--
--   Decomposition status. A corresponding proof sketch reduces this node to smaller mathematical subclaims. The checked reduction uses 2 subclaims: response centered sampling quadratic coefficient rate bound from sign scaled base event; quadratic coefficient response sign rate absorbed by A0 sample bound.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem
    response_centered_sampling_quadratic_coefficient_threshold_from_base_entry_scale
    (Cfixed Cbase Cresp : ℝ) :
    0 < Cfixed → 0 < Cbase → 0 < Cresp →
    ∃ Cthreshold : ℝ, 0 < Cthreshold ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ → A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              (β * Real.log (↑(max n₁ n₂))) →
        ∀ (Omega : Finset (Fin n₁ × Fin n₂))
          (B Y : Matrix (Fin n₁) (Fin n₂) ℝ)
          (Rop : Matrix (Fin n₁) (Fin n₂) ℝ →
            Matrix (Fin n₁) (Fin n₂) ℝ),
        Y =
          Rop (centeredSamplingFluctuation Omega
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) B) →
        (∀ X : Matrix (Fin n₁) (Fin n₂) ℝ,
          spectralNorm (Rop X) ≤ Cresp * spectralNorm X) →
        entrySupNorm B ≤
          Cbase * μ₀ * ((r : ℝ) / (↑(max n₁ n₂))) *
            entrySupNorm (signMatrix S) →
        CenteredSamplingSpectralBound Omega
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) B
            (Cfixed * Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              entrySupNorm B) →
        entrySupNorm Y ≤ Cthreshold * Real.rpow lam (-1) := by
  sorry

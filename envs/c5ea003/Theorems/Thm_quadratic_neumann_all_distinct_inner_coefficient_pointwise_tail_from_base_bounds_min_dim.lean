-- Prove2me | Theorems.Thm_quadratic_neumann_all_distinct_inner_coefficient_pointwise_tail_from_base_bounds_min_dim
-- name    : quadratic_neumann_all_distinct_inner_coefficient_pointwise_tail_from_base_bounds_min_dim
-- status  : Proved
-- author  : @Minghui
-- created : 2026-06-30T12:46:44.796484+00:00
-- url     : https://prove2.me/theorems/99ce3339-c366-457a-82ff-734c16ddb59e
-- statement:
--   Corrected min-dimension pointwise Bernstein child for the all-distinct inner coefficient in the quadratic Neumann term.
--
--   Primary reference: Candes--Recht, *Exact Matrix Completion via Convex Optimization*, PDF p. 28, Section 6.2, Lemma 6.6, equations (6.15)--(6.17), and PDF p. 30, Section 6.3, equation (6.20).
--
--   Mathematical statement and notation: let $n=\max(n_1,n_2)$ and let $p=m/(n_1n_2)$. The sample set $\Omega_3$ is drawn from the independent Bernoulli model with rate $p$, represented in Lean by `bernoulliEventProb p`. Let $S$ be the SVD data for an $n_1\times n_2$ rank-$r$ matrix, with incoherence hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$. For coordinates $w_1,w_2\in [n_1]\times[n_2]$, equation (6.20) writes the inner all-distinct coefficient as the centered scalar sampling fluctuation
--   $$
--   G_{w_1,w_2}(\Omega_3)
--   = \sum_{i,j}(1_{(i,j)\in\Omega_3}-p)B^{\rm all}_{w_1,w_2}(i,j).
--   $$
--   Assume the corrected rectangular Lemma 6.6 base bounds
--   $$
--   \|B^{\rm all}_{w_1,w_2}\|_\infty
--   \le C_{\rm entry}\mu_1\sqrt{\frac r{n_1n_2}}{\mu_0r\over\min(n_1,n_2)},
--   $$
--
--   and
--   $$
--   \|B^{\rm all}_{w_1,w_2}\|_F
--   \le C_{\rm fro}\mu_1\sqrt{\frac r{n_1n_2}}\sqrt{\frac{\mu_0r}{\min(n_1,n_2)}}.
--   $$
--   Under the Lemma 6.6 sample lower bound
--   $$
--   m\ge \lambda\mu_0^{4/3}n r^{4/3}\beta\log n,
--   $$
--   the fixed coordinate pair satisfies the pointwise tail
--   $$
--   \mathbb P_p\{|G_{w_1,w_2}(\Omega_3)|\le C_{\rm point}\lambda^{-1/2}\}
--   \ge 1-c_{\rm point}n^{-\beta}.
--   $$
--   Here $p,n,\Omega_3,\mu_0,\mu_1$, the Bernoulli probability model, and the coefficient family are explicitly named; $Z(\Omega)$ and `successProb` do not appear in this local coefficient theorem.
--
--   Formalization note: this is a source-derived theorem, not a theorem stated verbatim in the paper and not a formal bridge. It packages the scalar Bernstein calculation from Lemma 6.6 with the corrected min-dimension base estimates for the all-distinct inner coefficient from equation (6.20). It is intended as the source-backed analytic child for the formal bridge `quadratic_neumann_all_distinct_inner_coefficients_from_base_bounds_min_dim_shifted`.
-- source:
--   Candes--Recht, *Exact Matrix Completion via Convex Optimization*, PDF p. 28, Section 6.2, Lemma 6.6, equations (6.15)--(6.17); PDF p. 30, Section 6.3, equation (6.20).

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_all_distinct_inner_coefficient_pointwise_tail_from_base_bounds_min_dim
    (Centry Cfro : ℝ) :
    0 < Centry → 0 < Cfro →
    ∃ Cpoint cpoint : ℝ, 0 < Cpoint ∧ 0 < cpoint ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              (β * Real.log (↑(max n₁ n₂))) →
        (∀ (Omega3 : Finset (Fin n₁ × Fin n₂))
            (w1 w2 : Fin n₁ × Fin n₂),
          quadraticAllDistinctInnerCoefficient Omega3 S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1 w2 =
            matrixEntrySum
              (centeredSamplingFluctuation Omega3
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (quadraticAllDistinctInnerBaseMatrix S w1 w2))) →
        (∀ w1 w2 : Fin n₁ × Fin n₂,
          entrySupNorm (quadraticAllDistinctInnerBaseMatrix S w1 w2) ≤
            Centry * μ₁ *
              Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) →
        (∀ w1 w2 : Fin n₁ × Fin n₂,
          frobeniusNorm (quadraticAllDistinctInnerBaseMatrix S w1 w2) ≤
            Cfro * μ₁ *
              Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) →
        ∀ w1 w2 : Fin n₁ × Fin n₂,
          bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega3 =>
                |quadraticAllDistinctInnerCoefficient Omega3 S
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1 w2| ≤
                  Cpoint * Real.rpow lam (-((1 : ℝ) / 2))) ≥
            1 - cpoint * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry

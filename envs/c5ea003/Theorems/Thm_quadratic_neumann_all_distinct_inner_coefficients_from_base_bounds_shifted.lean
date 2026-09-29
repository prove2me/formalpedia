-- Prove2me | Theorems.Thm_quadratic_neumann_all_distinct_inner_coefficients_from_base_bounds_shifted
-- name    : quadratic_neumann_all_distinct_inner_coefficients_from_base_bounds_shifted
-- status  : Proved
-- author  : @Minghui
-- created : 2026-06-26T21:04:21.159702+00:00
-- url     : https://prove2.me/theorems/7f9419c1-fd93-4d64-afaa-ea64821003ce
-- statement:
--   Source:
--   Candès--Recht, *Exact Matrix Completion via Convex Optimization*, PDF p. 28, Section 6.2, Lemma 6.6, equations (6.15)--(6.17), and PDF p. 30, Section 6.3, equation (6.20).
--
--   Mathematical statement:
--   Let $n=\max(n_1,n_2)$ and let $p=m/(n_1n_2)$ be the Bernoulli sampling rate.  Let $S$ be rank-$r$ SVD data for $M$, with incoherence hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$.  For the all-distinct quadratic Neumann inner coefficient family
--   $$
--   H_{w_1,w_2}(\Omega_3)
--   =\operatorname{quadraticAllDistinctInnerCoefficient}(\Omega_3,S,p,w_1,w_2),
--   $$
--   assume the centered-fluctuation representation from equation (6.20), and assume deterministic base-matrix bounds
--   $$
--   \|B_{w_1,w_2}\|_\infty\le C_{\rm entry}\mu_0^2(r/n)^2,
--   \qquad
--   \|B_{w_1,w_2}\|_F\le C_{\rm frob}\mu_0^{3/2}(r/n)^{3/2}.
--   $$
--   If the usual Lemma 4.6 sample lower bound holds both at exponent $\beta$ and at the union-bound-shifted exponent $\beta+4$,
--   $$
--   m\ge \lambda\mu_0^{4/3}n r^{4/3}\,\beta\log n,
--   \qquad
--   m\ge \lambda\mu_0^{4/3}n r^{4/3}\, (\beta+4)\log n,
--   $$
--   then there are universal positive constants $C_{\rm inner},c_{\rm inner}$ such that
--   $$
--   \mathbb P_p\left\{\forall w_1,w_2,
--   |H_{w_1,w_2}(\Omega_3)|\le C_{\rm inner}\lambda^{-1/2}\right\}
--   \ge 1-c_{\rm inner}n^{-\beta}.
--   $$
--   Here $\Omega_3$ is a Bernoulli sample set.  The quantities $\mu_0,\mu_1$ are the Candes--Recht coherence parameters, and $Z(\Omega)$ does not appear in this Neumann coefficient bridge.
--
--   Formalization note:
--   This is a formal bridge, not a theorem stated verbatim in the paper.  It repairs the stale unshifted uniformization edge under `quadratic_neumann_all_distinct_inner_coefficients_from_base_bounds` by explicitly carrying the $\beta+4$ pointwise-tail/sample floor needed for the ordered-pair union bound.  The source-backed parent ingredients are the proved pointwise Bernstein node `quadratic_neumann_all_distinct_inner_coefficient_pointwise_tail_from_base_bounds`, whose source is Candès--Recht PDF p. 28, Lemma 6.6, equations (6.15)--(6.17), and the proved shifted uniformization node `quadratic_neumann_all_distinct_inner_coefficients_uniform_from_shifted_pointwise_tails`, whose source context is PDF p. 30, equation (6.20).
-- source:
--   Candès--Recht, Exact Matrix Completion via Convex Optimization, PDF p. 28, Section 6.2, Lemma 6.6, equations (6.15)--(6.17), and PDF p. 30, Section 6.3, equation (6.20).

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_all_distinct_inner_coefficients_from_base_bounds_shifted
    (Centry Cfro : ℝ) :
    0 < Centry → 0 < Cfro →
    ∃ Cinner cinner : ℝ, 0 < Cinner ∧ 0 < cinner ∧
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
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              ((β + 4) * Real.log (↑(max n₁ n₂))) →
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
            Centry * μ₀ ^ 2 *
              (((r : ℝ) / (↑(max n₁ n₂))) ^ 2)) →
        (∀ w1 w2 : Fin n₁ × Fin n₂,
          frobeniusNorm (quadraticAllDistinctInnerBaseMatrix S w1 w2) ≤
            Cfro * Real.rpow μ₀ ((3 : ℝ) / 2) *
              Real.rpow ((r : ℝ) / (↑(max n₁ n₂))) ((3 : ℝ) / 2)) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega3 =>
              QuadraticAllDistinctInnerCoefficientBound Omega3 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (Cinner * Real.rpow lam (-((1 : ℝ) / 2)))) ≥
          1 - cinner * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry

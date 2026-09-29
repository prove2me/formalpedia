-- Prove2me | Theorems.Thm_quadratic_neumann_all_distinct_inner_coefficients_from_base_bounds_min_dim_shifted
-- name    : quadratic_neumann_all_distinct_inner_coefficients_from_base_bounds_min_dim_shifted
-- status  : Proved
-- author  : @Minghui
-- created : 2026-06-30T12:49:03.253472+00:00
-- url     : https://prove2.me/theorems/9e56cb74-0b5b-40b2-ac0c-90ad54beb5ae
-- statement:
--   Formal bridge from the corrected min-dimension pointwise all-distinct inner coefficient tail to the simultaneous coefficient event with the required ordered-pair union-bound shift.
--
--   Primary reference: Candes--Recht, *Exact Matrix Completion via Convex Optimization*, PDF p. 28, Section 6.2, Lemma 6.6, equations (6.15)--(6.17), the union-bound discussion after equation (6.17), and PDF p. 30, Section 6.3, equation (6.20).
--
--   Mathematical statement and notation: set $n=\max(n_1,n_2)$ and $p=m/(n_1n_2)$. The event is over the Bernoulli sample $\Omega_3$ with probability `bernoulliEventProb p`. For SVD data $S$ satisfying $A0(S,\mu_0)$ and $A1(S,\mu_1)$, equation (6.20) identifies each all-distinct inner coefficient as
--   $$
--   G_{w_1,w_2}(\Omega_3)
--   = \sum_{i,j}(1_{(i,j)\in\Omega_3}-p)B^{\rm all}_{w_1,w_2}(i,j).
--   $$
--   Assume the corrected min-dimension entry and Frobenius bounds for $B^{\rm all}_{w_1,w_2}$ and the sample lower bound both at exponent $\beta$ and at shifted exponent $\beta+4$:
--   $$
--   m\ge \lambda\mu_0^{4/3}n r^{4/3}\beta\log n,
--   \qquad
--   m\ge \lambda\mu_0^{4/3}n r^{4/3}(\beta+4)\log n.
--   $$
--   Then, after applying the pointwise child at exponent $\beta+4$ and paying the ordered-pair union-bound cost $(n_1n_2)^2\le n^4$, the simultaneous event holds:
--   $$
--   \mathbb P_p\{\forall w_1,w_2, |G_{w_1,w_2}(\Omega_3)|\le C_{\rm inner}\lambda^{-1/2}\}
--   \ge 1-c_{\rm inner}n^{-\beta}.
--   $$
--   Here $p,n,\Omega_3,\mu_0,\mu_1$, the Bernoulli model, and the coefficient family are named explicitly. $Z(\Omega)$ and fixed-cardinality `successProb` do not appear in this local coefficient bridge.
--
--   Formalization note: this is a formal bridge, not a theorem appearing verbatim in the paper. It should import the source-backed pointwise child `quadratic_neumann_all_distinct_inner_coefficient_pointwise_tail_from_base_bounds_min_dim` and the already proved source-backed uniformization child `quadratic_neumann_all_distinct_inner_coefficients_uniform_from_shifted_pointwise_tails` (`c325fcc3-f5e1-48f4-acdb-12c7ae7ea619`). The bridge replaces the stale old route through `quadratic_neumann_all_distinct_inner_coefficients_from_base_bounds`, whose accepted sketch uses the deprecated unshifted uniformization child.
-- source:
--   Formal bridge. Source-backed analytic child: Candes--Recht, *Exact Matrix Completion via Convex Optimization*, PDF p. 28, Section 6.2, Lemma 6.6, equations (6.15)--(6.17); PDF p. 30, Section 6.3, equation (6.20). The ordered-pair union-bound child is the proved source-backed theorem `quadratic_neumann_all_distinct_inner_coefficients_uniform_from_shifted_pointwise_tails`.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_all_distinct_inner_coefficients_from_base_bounds_min_dim_shifted
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
            Centry * μ₁ *
              Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) →
        (∀ w1 w2 : Fin n₁ × Fin n₂,
          frobeniusNorm (quadraticAllDistinctInnerBaseMatrix S w1 w2) ≤
            Cfro * μ₁ *
              Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega3 =>
              QuadraticAllDistinctInnerCoefficientBound Omega3 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (Cinner * Real.rpow lam (-((1 : ℝ) / 2)))) ≥
          1 - cinner * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry

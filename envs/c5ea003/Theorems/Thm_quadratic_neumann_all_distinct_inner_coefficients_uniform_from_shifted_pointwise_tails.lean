-- Prove2me | Theorems.Thm_quadratic_neumann_all_distinct_inner_coefficients_uniform_from_shifted_pointwise_tails
-- name    : quadratic_neumann_all_distinct_inner_coefficients_uniform_from_shifted_pointwise_tails
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-21T22:30:41.734676+00:00
-- url     : https://prove2.me/theorems/c325fcc3-f5e1-48f4-acdb-12c7ae7ea619
-- statement:
--   This is the corrected finite-uniformization theorem for the inner coefficients of the all-distinct quadratic Neumann term.
--
--   Matrix-completion notation. Let $M\in\mathbb R^{n_1\times n_2}$ have rank data $S$, let $n=\max(n_1,n_2)$, and let $\Omega$ be sampled in the Bernoulli model with parameter
--   $$
--   p=\frac{m}{n_1n_2}.
--   $$
--   The assumptions $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht coherence hypotheses, and $\lambda\ge1$ is the auxiliary sample-size parameter used in Lemma 4.6.
--
--   Claim. Suppose that for every ordered pair of coordinates $(w_1,w_2)$ the inner coefficient in the all-distinct quadratic term obeys the pointwise tail
--   $$
--   \mathbb P_p\left\{\left|H_{w_1,w_2}(\Omega)\right|\le C_{\rm point}\lambda^{-1/2}\right\}
--   \ge 1-c_{\rm point}n^{-(\beta+4)}.
--   $$
--   Then, after enlarging only universal constants, all ordered-pair coefficients obey the same threshold simultaneously with final failure exponent $\beta$:
--   $$
--   \mathbb P_p\left\{\forall w_1,w_2,\ \left|H_{w_1,w_2}(\Omega)\right|\le C_{\rm inner}\lambda^{-1/2}\right\}
--   \ge 1-c_{\rm inner}n^{-\beta}.
--   $$
--
--   The four-power shift from $\beta+4$ to $\beta$ is not cosmetic: it is exactly the cost of the ordered-pair union bound, since $(n_1n_2)^2\le n^4$.
--
--   Source context. Candes-Recht 2008, PDF p. 28, Lemma 6.6 and equation (6.15), gives a pointwise coefficient tail; PDF p. 29 applies a union bound after equation (6.17); PDF p. 30, equation (6.20), identifies the ordered-pair coefficient structure in the all-distinct quadratic Neumann term.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_all_distinct_inner_coefficients_uniform_from_shifted_pointwise_tails
    (Cpoint cpoint : ℝ) :
    0 < Cpoint → 0 < cpoint →
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
        (∀ w1 w2 : Fin n₁ × Fin n₂,
          bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega3 =>
                |quadraticAllDistinctInnerCoefficient Omega3 S
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1 w2| ≤
                  Cpoint * Real.rpow lam (-((1 : ℝ) / 2))) ≥
            1 - cpoint * Real.rpow (↑(max n₁ n₂)) (-(β + 4))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega3 =>
              QuadraticAllDistinctInnerCoefficientBound Omega3 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (Cinner * Real.rpow lam (-((1 : ℝ) / 2)))) ≥
          1 - cinner * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry

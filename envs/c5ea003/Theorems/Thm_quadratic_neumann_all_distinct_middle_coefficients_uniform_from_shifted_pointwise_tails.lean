-- Prove2me | Theorems.Thm_quadratic_neumann_all_distinct_middle_coefficients_uniform_from_shifted_pointwise_tails
-- name    : quadratic_neumann_all_distinct_middle_coefficients_uniform_from_shifted_pointwise_tails
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-21T23:21:42.761829+00:00
-- url     : https://prove2.me/theorems/9c750de5-e2a8-48c7-8ba5-2c78566d18d4
-- statement:
--   This is the corrected coordinate-uniformization step for the middle coefficient in the all-distinct quadratic Neumann term.
--
--   Fix the inner sample $\Omega_3$ and suppose the inner coefficients have already been uniformly bounded. For each outer coordinate $w_1$, assume the pointwise middle coefficient tail
--   $$
--   \mathbb P\left\{|H_{w_1}(\Omega_2,\Omega_3)|\le (C_{\rm point}C_{\rm inner})\lambda^{-1}\right\}
--   \ge 1-c_{\rm point}n^{-(\beta+2)},\qquad n=\max(n_1,n_2).
--   $$
--   Then the simultaneous coefficient event over all $w_1\in \operatorname{Fin} n_1\times\operatorname{Fin} n_2$ holds with final failure scale $n^{-\beta}$:
--   $$
--   \mathbb P\left\{\forall w_1,\ |H_{w_1}(\Omega_2,\Omega_3)|\le (C_{\rm cond}C_{\rm inner})\lambda^{-1}\right\}
--   \ge 1-c_{\rm cond}n^{-\beta}.
--   $$
--   The shift from $\beta+2$ to $\beta$ is exactly the cost of the coordinate union bound, since $n_1n_2\le n^2$.
--
--   Source: Candes-Recht 2008, PDF p. 29 after equation (6.17), and PDF p. 30 equation (6.20) for the all-distinct quadratic coefficient decomposition.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_all_distinct_middle_coefficients_uniform_from_shifted_pointwise_tails
    (Cpoint cpoint : ℝ) :
    0 < Cpoint → 0 < cpoint →
    ∃ Ccond ccond : ℝ, 0 < Ccond ∧ 0 < ccond ∧
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
        ∀ Cinner : ℝ, 0 < Cinner →
        ∀ Omega3 : Finset (Fin n₁ × Fin n₂),
        QuadraticAllDistinctInnerCoefficientBound Omega3 S
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (Cinner * Real.rpow lam (-((1 : ℝ) / 2))) →
        (∀ w1 : Fin n₁ × Fin n₂,
          bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega2 =>
                |quadraticAllDistinctMiddleCoefficient Omega2 Omega3 S
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1| ≤
                  (Cpoint * Cinner) * Real.rpow lam (-1)) ≥
            1 - cpoint * Real.rpow (↑(max n₁ n₂)) (-(β + 2))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega2 =>
              QuadraticAllDistinctMiddleCoefficientBound Omega2 Omega3 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                ((Ccond * Cinner) * Real.rpow lam (-1))) ≥
          1 - ccond * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry

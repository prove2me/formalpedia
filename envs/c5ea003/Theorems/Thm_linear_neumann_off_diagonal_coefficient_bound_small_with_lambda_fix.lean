-- Prove2me | Theorems.Thm_linear_neumann_off_diagonal_coefficient_bound_small_with_lambda_fix
-- name    : linear_neumann_off_diagonal_coefficient_bound_small_with_lambda_fix
-- status  : Proved
-- author  : @allychan327
-- created : 2026-06-25T02:19:33.728259+00:00
-- url     : https://prove2.me/theorems/27731a86-25c8-41a0-9c75-e17d1f8dbb3d
-- statement:
--   CR-faithful corrected off-diagonal first-Neumann coefficient bound (small-with-$\lambda$). Same as `linear_neumann_off_diagonal_coefficient_bound_small_with_lambda` but with the $\mu_0$-linear sample lower bound $\max(\mu_0,\mu_1)$ (CR2009 Lemma 6.6 eq 6.15 / Thm 1.3 eq 1.9). With probability $\ge 1-c_{coef}\,n^{-\beta}$ the off-diagonal first-Neumann coefficient spectral norm is bounded by $C_{coef}\,\mu_1\sqrt{r/(n_1 n_2)}\sqrt{\mu_0 n r\beta\log n/m}$.
-- source:
--   https://arxiv.org/abs/0805.4471 (Candes-Recht 2009) Lemma 6.6 eq 6.15; Thm 1.3 eq 1.9

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem linear_neumann_off_diagonal_coefficient_bound_small_with_lambda_fix :
    ∃ Ccoef ccoef : ℝ, 0 < Ccoef ∧ 0 < ccoef ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          lam * μ₁ * max μ₀ μ₁ *
            (↑(max n₁ n₂)) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega2 =>
              LinearNeumannOffDiagonalCoefficientBound Omega2 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (Ccoef * μ₁ *
                  Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                    Real.sqrt
                      ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
                          (β * Real.log (↑(max n₁ n₂)))) / (m : ℝ)))) ≥
          1 - ccoef * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry

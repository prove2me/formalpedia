-- Prove2me | Theorems.Thm_linear_neumann_off_diagonal_coefficient_bound_from_bernstein_base_bounds_fix
-- name    : linear_neumann_off_diagonal_coefficient_bound_from_bernstein_base_bounds_fix
-- status  : Proved
-- author  : @allychan327
-- created : 2026-06-25T02:17:35.326511+00:00
-- url     : https://prove2.me/theorems/982c49ed-1536-4490-a6b4-5a0cbdc3edc6
-- statement:
--   CR-faithful corrected off-diagonal first-Neumann coefficient Bernstein bound. Same as `linear_neumann_off_diagonal_coefficient_bound_from_bernstein_base_bounds` but with the $\mu_0$-linear sample lower bound $\max(\mu_0,\mu_1)$ (CR2009 Lemma 6.6 / Thm 1.3 eq 1.9). Given deterministic base entry-sup and Frobenius bounds and the centered-scalar representation, a union of per-cell two-term Bernstein tails over $n_1 n_2$ output cells gives, with probability $\ge 1-c_{coef}\,n^{-\beta}$, the clean coefficient bound.
-- source:
--   https://arxiv.org/abs/0805.4471 (Candes-Recht 2009) Lemma 6.6 eq 6.15; Thm 1.3 eq 1.9

import Definitions.Def_linear_neumann_offdiag_bernstein
open MatrixCompletion

theorem linear_neumann_off_diagonal_coefficient_bound_from_bernstein_base_bounds_fix
    (Centry Cfro : ℝ) :
    0 < Centry → 0 < Cfro →
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
        (∀ (Omega2 : Finset (Fin n₁ × Fin n₂))
            (w : Fin n₁ × Fin n₂),
          linearNeumannOffDiagonalCoefficientMatrix Omega2 S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w.1 w.2 =
            matrixEntrySum
              (centeredSamplingFluctuation Omega2
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (linearNeumannOffDiagonalCoefficientBaseMatrix S w))) →
        (∀ w : Fin n₁ × Fin n₂,
          entrySupNorm
              (linearNeumannOffDiagonalCoefficientBaseMatrix S w) ≤
            Centry * μ₁ *
              Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                (μ₀ * (r : ℝ) / (↑(max n₁ n₂)))) →
        (∀ w : Fin n₁ × Fin n₂,
          frobeniusNorm
              (linearNeumannOffDiagonalCoefficientBaseMatrix S w) ≤
            Cfro * μ₁ *
              Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                Real.sqrt
                  (μ₀ * (r : ℝ) / (↑(max n₁ n₂)))) →
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

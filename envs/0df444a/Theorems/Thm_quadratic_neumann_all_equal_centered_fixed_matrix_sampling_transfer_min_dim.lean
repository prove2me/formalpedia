-- Prove2me | Theorems.Thm_quadratic_neumann_all_equal_centered_fixed_matrix_sampling_transfer_min_dim
-- name    : quadratic_neumann_all_equal_centered_fixed_matrix_sampling_transfer_min_dim
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-02T14:15:42.589776+00:00
-- url     : https://prove2.me/theorems/c28ae4f7-a140-4532-853b-e5e10da349c1
-- statement:
--   Min-dimension transfer leaf for the centered all-equal term in Candes-Recht Lemma 4.6. In equation (6.21), the all-equal cubic Bernoulli term splits into a centered fixed-matrix fluctuation and a deterministic mean term. This theorem is the deterministic/probabilistic transfer that applies the fixed-matrix centered sampling estimate to the centered part when the fixed base matrix has the corrected rectangular entry bound
--   $$
--   \|B\|_{\infty}\le C_{base}\mu_0^3\left(rac r{\min(n_1,n_2)}ight)^3.
--   $$
--   It absorbs that min-dimension scale and the scalar $p^{-2}(1-3p+3p^2)$ under the Lemma 4.6 sample lower bound
--   $$
--   m\ge \lambda\mu_0^{4/3}n r^{4/3}eta\log n,
--   \quad n=\max(n_1,n_2).
--   $$
--
--   Source: Candes-Recht 2008, PDF p. 30, equation (6.21), and the paragraph immediately following it where Theorem 6.3 is applied to the centered term. Formalization note: this is the corrected rectangular replacement for the old transfer route that was paired with the deprecated max-dimension base-entry theorem.
-- source:
--   Candes-Recht 2008, Exact Matrix Completion via Convex Optimization, PDF p. 30, equation (6.21), and the subsequent Theorem 6.3 application to the centered all-equal term.

import Definitions.Def_matrix_completion_neumann

open MatrixCompletion

/-- Min-dimension version of the transfer from the fixed all-equal matrix in
Candes-Recht equation (6.21) to the centered all-equal quadratic contribution.

Source: Candes-Recht 2008, PDF p. 30, equation (6.21), together with the
Theorem 6.3 fixed-matrix sampling estimate used immediately after (6.21).  This
is the corrected rectangular transfer leaf: the entry bound is stated with
`min n₁ n₂`, matching the proved rectangular base estimate rather than the
deprecated square/max-dimension bound. -/

theorem quadratic_neumann_all_equal_centered_fixed_matrix_sampling_transfer_min_dim
    (Cfixed Cbase : ℝ) :
    0 < Cfixed → 0 < Cbase →
    ∃ Ccent ccent : ℝ, 0 < Ccent ∧ 0 < ccent ∧
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
        (∀ Omega : Finset (Fin n₁ × Fin n₂),
          quadraticNeumannAllEqualCenteredContribution Omega S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) =
            ((((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) ^ 2 *
                (1 - 3 * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) +
                  3 * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) ^ 2)) •
              centeredSamplingFluctuation Omega
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (quadraticNeumannAllEqualBaseMatrix S)) →
        entrySupNorm (quadraticNeumannAllEqualBaseMatrix S) ≤
          Cbase * μ₀ ^ 3 * (((r : ℝ) / (↑(min n₁ n₂))) ^ 3) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              CenteredSamplingSpectralBound Omega
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (quadraticNeumannAllEqualBaseMatrix S)
                (Cfixed * Real.sqrt
                  ((β * (↑(max n₁ n₂)) *
                      Real.log (↑(max n₁ n₂))) /
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                  entrySupNorm (quadraticNeumannAllEqualBaseMatrix S))) ≥
          1 - (1 : ℝ) * Real.rpow (↑(max n₁ n₂)) (-β) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              spectralNorm
                (quadraticNeumannAllEqualCenteredContribution Omega S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                Ccent * Real.rpow lam (-((3 : ℝ) / 2))) ≥
          1 - ccent * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry

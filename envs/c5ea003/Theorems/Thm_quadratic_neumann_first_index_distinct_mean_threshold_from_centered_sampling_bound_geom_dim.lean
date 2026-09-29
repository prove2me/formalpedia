-- Prove2me | Theorems.Thm_quadratic_neumann_first_index_distinct_mean_threshold_from_centered_sampling_bound_geom_dim
-- name    : quadratic_neumann_first_index_distinct_mean_threshold_from_centered_sampling_bound_geom_dim
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-04T13:18:13.91524+00:00
-- url     : https://prove2.me/theorems/331f5696-8065-4044-b5c4-1a33258fff3f
-- statement:
--   Deterministic threshold for the first-index-distinct mean contribution at the honest geometric-mean coefficient scale: if the mean contribution equals $(1-p)\cdot p^{-1}(P_\Omega-p\mathcal I)(F)$, $\|F\|_\infty \le C_{coef}\,p^{-1}(\mu_0r/\min)(\mu_0r/\sqrt{n_1n_2})(1+\mu_0r/\min)$, and the Theorem 6.3 event $\|p^{-1}(P_\Omega-p\mathcal I)(F)\|\le C_f\sqrt{\beta n\log n/p}\,\|F\|_\infty$ holds, then under $m\ge\lambda\mu_0^{4/3}nr^{4/3}\beta\log n$ the mean contribution has spectral norm at most $C\lambda^{-3/2}$. Replaces the $(r/\max)^2$-scale variant quadratic_neumann_first_index_distinct_mean_threshold_from_centered_sampling_bound, whose coefficient hypothesis is not satisfiable by the actual mean coefficient matrix in the rectangular regime. Absorption: $p^{-3/2}\sqrt{\beta n\log n}\,(\mu_0r)^2/(\min\sqrt{n_1n_2}) \le \lambda^{-3/2}/(\beta\log n)$ using $p\ge\lambda\mu_0^{4/3}r^{4/3}\beta\log n/\min$ and $\max\cdot\min=n_1n_2$; the $(1+\mu_0r/\min)$ factor is killed by $\mu_0 r\le\mu_0^{4/3}r^{4/3}\le\min/(\lambda\beta\log n)$.
-- source:
--   Candes-Recht 2008, Section 6.3 case 2 (Lemma 6.8, eq. 6.22) rectangular form

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_first_index_distinct_mean_threshold_from_centered_sampling_bound_geom_dim
    (Cfixed Ccoef : ℝ) :
    0 < Cfixed → 0 < Ccoef →
    ∃ Cthreshold : ℝ, 0 < Cthreshold ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ → 1 ≤ μ₀ → A0 S μ₀ →
        (m : ℝ) ≥ lam * Real.rpow μ₀ ((4 : ℝ) / 3) * (↑(max n₁ n₂)) *
          Real.rpow (r : ℝ) ((4 : ℝ) / 3) * (β * Real.log (↑(max n₁ n₂))) →
        ∀ Omega : Finset (Fin n₁ × Fin n₂),
        quadraticNeumannFirstIndexDistinctMeanContribution Omega S
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) =
          (1 - ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) •
            centeredSamplingFluctuation Omega ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (quadraticFirstIndexDistinctMeanCoefficientMatrix S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) →
        entrySupNorm (quadraticFirstIndexDistinctMeanCoefficientMatrix S
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
          Ccoef * (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) *
            (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) *
              (μ₀ * (r : ℝ) / Real.sqrt ((n₁ : ℝ) * (n₂ : ℝ))) *
                (1 + μ₀ * (r : ℝ) / (↑(min n₁ n₂))) →
        CenteredSamplingSpectralBound Omega ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (quadraticFirstIndexDistinctMeanCoefficientMatrix S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))
            (Cfixed * Real.sqrt
              ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              entrySupNorm (quadraticFirstIndexDistinctMeanCoefficientMatrix S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))) →
        spectralNorm (quadraticNeumannFirstIndexDistinctMeanContribution Omega S
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
          Cthreshold * Real.rpow lam (-((3 : ℝ) / 2)) := by sorry

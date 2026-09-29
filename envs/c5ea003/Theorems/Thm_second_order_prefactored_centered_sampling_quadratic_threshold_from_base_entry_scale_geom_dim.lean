-- Prove2me | Theorems.Thm_second_order_prefactored_centered_sampling_quadratic_threshold_from_base_entry_scale_geom_dim
-- name    : second_order_prefactored_centered_sampling_quadratic_threshold_from_base_entry_scale_geom_dim
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-04T12:38:30.277913+00:00
-- url     : https://prove2.me/theorems/851a9806-0583-4494-948f-5f7fe741068a
-- statement:
--   Corrected (geometric-mean scale) second-order prefactored centered-sampling threshold for the all-equal quadratic Neumann term, CR08 (6.21): if $Y = p^{-2}(1-3p+3p^2)\cdot p^{-1}(P_\Omega-p\mathcal I)(B)$ with $\|B\|_\infty \le C_b\,\mu_0^3r^3/(\min(n_1,n_2)^2\sqrt{n_1n_2})$, the Theorem 6.3 event $\|p^{-1}(P_\Omega-p\mathcal I)(B)\| \le C_f\sqrt{\beta n\log n/p}\,\|B\|_\infty$ holds ($n=\max(n_1,n_2)$), and $m \ge \lambda\mu_0^{4/3}nr^{4/3}\beta\log n$, then $\|Y\| \le C\lambda^{-3/2}$. The chain: $\|Y\| \le p^{-5/2}\sqrt{\beta n\log n}\cdot C_bC_f\mu_0^3r^3/(\min^2\sqrt{n_1n_2}) \le C_fC_b\,\lambda^{-5/2}\mu_0^{-1/3}r^{-1/3}(\beta\log n)^{-2} \le C_fC_b\lambda^{-3/2}$, using $p \ge \lambda\mu_0^{4/3}r^{4/3}\beta\log n/\min(n_1,n_2)$ and $\max\cdot\min = n_1n_2$. WARNING: the $(r/\min)^3$ variant of this statement (second_order_prefactored_centered_sampling_quadratic_threshold_from_base_entry_scale_min_dim, 17b086f9) is FALSE in the rectangular regime $\min \asymp \beta\log\max$ (counterexample: $p=1$, $\Omega=\emptyset$, $B$ the constant matrix at the allowed scale, $\|Y\|=\sqrt{n_1n_2}/\min^3 \to \infty$); the geometric mean $\sqrt{n_1n_2}$ is exactly what reconciles the entry scale with the spectral growth.
-- source:
--   Candes-Recht 2008, Exact Matrix Completion via Convex Optimization, Section 6.3 (proof of Lemma 4.6, all-equal case, eq. 6.21)

import Definitions.Def_matrix_completion_tangent
import Mathlib.Analysis.Complex.ExponentialBounds
open MatrixCompletion

theorem second_order_prefactored_centered_sampling_quadratic_threshold_from_base_entry_scale_geom_dim
    (Cfixed Cbase : ℝ) :
    0 < Cfixed → 0 < Cbase →
    ∃ Cthreshold : ℝ, 0 < Cthreshold ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (μ₀ : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ →
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              (β * Real.log (↑(max n₁ n₂))) →
        ∀ (Omega : Finset (Fin n₁ × Fin n₂))
          (B Y : Matrix (Fin n₁) (Fin n₂) ℝ),
        Y =
          ((((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) ^ 2 *
              (1 - 3 * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) +
                3 * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) ^ 2)) •
            centeredSamplingFluctuation Omega
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) B →
        entrySupNorm B ≤
          Cbase * μ₀ ^ 3 * (r : ℝ) ^ 3 /
            ((↑(min n₁ n₂)) ^ 2 * Real.sqrt ((n₁ : ℝ) * (n₂ : ℝ))) →
        CenteredSamplingSpectralBound Omega
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) B
            (Cfixed * Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              entrySupNorm B) →
        spectralNorm Y ≤
          Cthreshold * Real.rpow lam (-((3 : ℝ) / 2)) := by sorry

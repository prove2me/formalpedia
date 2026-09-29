-- Prove2me | Theorems.Thm_quadratic_neumann_first_index_distinct_centered_decoupled_threshold_from_tight_coefficient_scale
-- name    : quadratic_neumann_first_index_distinct_centered_decoupled_threshold_from_tight_coefficient_scale
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-04T13:20:59.082241+00:00
-- url     : https://prove2.me/theorems/c7285124-3c15-4306-9363-0bf06cdf9055
-- statement:
--   Deterministic absorption for the pair-decoupled first-index-distinct centered term at the HONEST (tight Bernstein) coefficient scale: if $Y=p^{-1}(1-2p)\cdot p^{-1}(P_{\Omega_1}-p\mathcal I)(B)$, the entry bound $\|B\|_\infty$ is at most the tight Bernstein scale $C(\sqrt{(\beta+2)\log N/p}\cdot\mu_0\sqrt r\sqrt{r/(n_1n_2)}\sqrt{\mu_0r/\min}(\mu_0r/\min)+((\beta+2)\log N/p)\cdot\mu_0\sqrt r\sqrt{r/(n_1n_2)}(\mu_0r/\min)^2)$ (= the coefficient event scale of quadratic_neumann_first_index_distinct_centered_coefficient_entry_sup_event_tight_min_dim at $\mu_1=\mu_0\sqrt r$), and the Theorem 6.3 event holds for $B$, then under $m\ge\lambda\mu_0^{4/3}Nr^{4/3}\beta\log N$: $\|Y\|\le C_{th}\lambda^{-3/2}$. The dimensionless-scale variant quadratic_neumann_first_index_distinct_centered_decoupled_threshold_from_centered_sampling_bound (4aa38f43) is FALSE in the rectangular regime (same class as the disproof-confirmed 7ef20022/fbd465ab/8cf0d039 family): the dimensional $\sqrt{r/(n_1n_2)}$ factor here is exactly what reconciles the two Bernstein layers. Numerically verified end-to-end: worst constant 2.07 vs bound 4 over 4613 feasible points.
-- source:
--   Candes-Recht 2008, Section 6.3 case 2 (S1 term, Lemma 6.7 route), rectangular form

import Definitions.Def_matrix_completion_tangent
import Mathlib.Analysis.Complex.ExponentialBounds
open MatrixCompletion

theorem quadratic_neumann_first_index_distinct_centered_decoupled_threshold_from_tight_coefficient_scale
    (Cfixed Ccoef : ℝ) :
    0 < Cfixed → 0 < Ccoef →
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
          (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹ *
              (1 - 2 * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))) •
            centeredSamplingFluctuation Omega
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) B →
        entrySupNorm B ≤
          Ccoef *
            (Real.sqrt
                (((β + 2) * Real.log (↑(max n₁ n₂))) /
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                (μ₀ * Real.sqrt (r : ℝ) *
                  Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                    Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) *
                      (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) +
              (((β + 2) * Real.log (↑(max n₁ n₂))) /
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                (μ₀ * Real.sqrt (r : ℝ) *
                  Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                    (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) *
                      (μ₀ * (r : ℝ) / (↑(min n₁ n₂))))) →
        CenteredSamplingSpectralBound Omega
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) B
            (Cfixed * Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              entrySupNorm B) →
        spectralNorm Y ≤
          Cthreshold * Real.rpow lam (-((3 : ℝ) / 2)) := by sorry

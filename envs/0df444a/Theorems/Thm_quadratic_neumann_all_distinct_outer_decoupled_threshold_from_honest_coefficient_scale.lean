-- Prove2me | Theorems.Thm_quadratic_neumann_all_distinct_outer_decoupled_threshold_from_honest_coefficient_scale
-- name    : quadratic_neumann_all_distinct_outer_decoupled_threshold_from_honest_coefficient_scale
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-04T14:13:45.264526+00:00
-- url     : https://prove2.me/theorems/ba304666-3781-4586-ab2a-257fad4b19f2
-- statement:
--   Honest replacement for the FALSE dimensionless outer threshold (8cf0d039) in the all-distinct (triple-decoupled) quadratic Neumann term, CR08 SS6.3 case 5: if $Y = p^{-1}(P_{\Omega_1}-p\mathcal I)(B)$ and $\|B\|_\infty$ is at most the honest nested-Bernstein middle-coefficient scale (the four-term dimensional bound of the Proved pair event quadratic_neumann_all_distinct_middle_coefficient_entry_sup_pair_event_honest_min_dim at $\mu_1=\mu_0\sqrt r$), then on the Theorem 6.3 event, under $m\ge\lambda\mu_0^{4/3}Nr^{4/3}\beta\log N$: $\|Y\|\le 36 C_fC_c\,\lambda^{-3/2}$. This is the $\lambda^{-3/2}$-TIGHT case of the SS6.3 ledger (leading monomial cancels exactly); numerically verified over 36507 feasible points, worst per-monomial ratios 0.71-0.9994 of the Lean constants.
-- source:
--   Candes-Recht 2008, Section 6.3 case 5 (all distinct, eq. 6.23), rectangular form

import Definitions.Def_matrix_completion_tangent
import Mathlib.Analysis.Complex.ExponentialBounds
open MatrixCompletion

theorem quadratic_neumann_all_distinct_outer_decoupled_threshold_from_honest_coefficient_scale
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
          centeredSamplingFluctuation Omega
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) B →
        entrySupNorm B ≤
          Ccoef *
            (Real.sqrt
                  (((β + 2) * Real.log (↑(max n₁ n₂))) /
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                (Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) *
                  (Real.sqrt
                        (((β + 4) * Real.log (↑(max n₁ n₂))) /
                          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                      (μ₀ * Real.sqrt (r : ℝ) *
                        Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                        Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) +
                    (((β + 4) * Real.log (↑(max n₁ n₂))) /
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                      (μ₀ * Real.sqrt (r : ℝ) *
                        Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                        (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))))) +
              (((β + 2) * Real.log (↑(max n₁ n₂))) /
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                ((μ₀ * (r : ℝ) / (↑(min n₁ n₂))) *
                  (Real.sqrt
                        (((β + 4) * Real.log (↑(max n₁ n₂))) /
                          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                      (μ₀ * Real.sqrt (r : ℝ) *
                        Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                        Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) +
                    (((β + 4) * Real.log (↑(max n₁ n₂))) /
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                      (μ₀ * Real.sqrt (r : ℝ) *
                        Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                        (μ₀ * (r : ℝ) / (↑(min n₁ n₂))))))) →
        CenteredSamplingSpectralBound Omega
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) B
            (Cfixed * Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              entrySupNorm B) →
        spectralNorm Y ≤
          Cthreshold * Real.rpow lam (-((3 : ℝ) / 2)) := by sorry

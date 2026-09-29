-- Prove2me | Theorems.Thm_talagrand_tangent_sampling_upper_tail_bound_dense
-- name    : talagrand_tangent_sampling_upper_tail_bound_dense
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-25T02:35:57.352513+00:00
-- url     : https://prove2.me/theorems/64395f10-3a62-4c3d-8c83-3a54dff06416
-- title:
--   Talagrand–Bennett upper-tail bound, density-threaded
-- statement:
--   **C2_dense — density-threaded two-sided Talagrand–Bennett upper-tail bound.** Density-correct version of `talagrand_tangent_sampling_upper_tail_bound` (46ee9864): under the CR Theorem 4.1 density $m\ge\beta\mu_0\max(n_1,n_2)r\log\max(n_1,n_2)$, the increment ($B$) and variance ($\sigma^2$) bounds, and $\mathbb{E}Z\le\mathrm{scale}(C_{\mathrm{expect}})$, the centered tangent sampling deviation satisfies the two-sided tail $\mathbb{P}(|Z-\mathbb{E}Z|>\mathrm{scale}(C_{\mathrm{tail}}))\le c\,\max(n_1,n_2)^{-\beta}$. This is the content node CR §9.1 Thm 9.1 eq.(9.2). It reduces onto the σ²-aware entropy-method spine (modified-LSI, Herbst, sub-gamma Bennett, density absorption) plus the carved residuals R1 (self-bounding conditions for the concrete sup — the genuine gap) and R2 (Bennett-log↔Bernstein bridge). The density-free version is false in sparse $m$; threading density is the fix.
-- source:
--   Candes–Recht 2009 (arXiv:0805.4471) §9.1 Theorem 9.1 / eq.(9.2), p.46; Talagrand 1996 (Invent.Math.126:505–563); Ledoux, Concentration of Measure, Cor 7.8; Bousquet 2002.

import Definitions.Def_matrix_completion_talagrand
open MatrixCompletion

theorem talagrand_tangent_sampling_upper_tail_bound_dense
    (Cexpect : ℝ) :
    0 < Cexpect →
    ∃ Ctail c : ℝ, 0 < Ctail ∧ 0 < c ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥ β * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
          Real.log (↑(max n₁ n₂)) →
        TangentSamplingTalagrandIncrementBound S
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (2 * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) / (m : ℝ)) →
        TangentSamplingTalagrandVarianceBound S
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (2 * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) / (m : ℝ)) →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              tangentSamplingDeviation Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
          tangentSamplingDeviationScale Cexpect β μ₀ (max n₁ n₂) r m →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              abs (tangentSamplingDeviation Omega S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) -
                bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                  (fun Omega' =>
                    tangentSamplingDeviation Omega' S
                      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))) >
              tangentSamplingDeviationScale Ctail β μ₀ (max n₁ n₂) r m) ≤
          c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry

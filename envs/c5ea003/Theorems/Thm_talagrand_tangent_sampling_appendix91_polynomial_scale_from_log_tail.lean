-- Prove2me | Theorems.Thm_talagrand_tangent_sampling_appendix91_polynomial_scale_from_log_tail
-- name    : talagrand_tangent_sampling_appendix91_polynomial_scale_from_log_tail
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-29T15:41:07.362434+00:00
-- url     : https://prove2.me/theorems/9d9be65e-945e-40e2-b34a-ccfaf7b71a21
-- statement:
--   This is the scalar conversion at the end of Candès--Recht Appendix 9.1: the exact logarithmic Talagrand tail implies the polynomial failure probability used in Theorem 4.2.
--
--   In the paper application,
--   $$B=\sigma^2=\frac{2\mu_0nr}{m},\qquad n=\max(n_1,n_2),\qquad \mathbb E_p Z\le1.$$
--   Assume the exact Theorem 9.1 tail
--   $$\mathbb P_p(|Z-\mathbb E_pZ|\le t)\ge 1-3\exp\left(-\frac{t}{KB}\log\left(1+\frac{Bt}{B+B\mathbb E_pZ}\right)\right)$$
--   for every $t\ge0$.  After choosing the universal sample constant large enough and assuming
--   $$m\ge C\mu_0nr\,\beta\log n,$$
--   the theorem concludes the Theorem 4.2 bound
--   $$\mathbb P_p\left(Z\le \mathbb E_pZ+C\sqrt{\frac{\mu_0nr\,\beta\log n}{m}}\right)\ge 1-cn^{-\beta}.$$
--   This node contains no new probability; it is the logarithmic-exponent and constant-absorption calculation.
--
--   Source location: Candès--Recht Appendix 9.1, PDF p. 47, from “Since $\mathbb E Z\le1$” through the substitution establishing equation (4.10).
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_talagrand
import Mathlib.Analysis.SpecialFunctions.Log.Basic
open MatrixCompletion

theorem talagrand_tangent_sampling_appendix91_polynomial_scale_from_log_tail
    (K : ℝ) :
    0 < K →
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ C' : ℝ, C ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → 0 < m → m ≤ n₁ * n₂ →
        1 ≤ μ₀ →
        (m : ℝ) ≥
          C' * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
            (β * Real.log (↑(max n₁ n₂))) →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              tangentSamplingDeviation Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤ 1 →
        TangentSamplingTalagrandIncrementBound S
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (2 * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) / (m : ℝ)) →
        TangentSamplingTalagrandVarianceBound S
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (2 * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) / (m : ℝ)) →
        (∀ t : ℝ, 0 ≤ t →
          bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega =>
                |tangentSamplingDeviation Omega S
                      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) -
                    bernoulliExpectation
                      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                      (fun Omega' =>
                        tangentSamplingDeviation Omega' S
                          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))| ≤ t) ≥
            1 -
              3 * Real.exp
                (-(t / (K *
                    (2 * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) / (m : ℝ)))) *
                  Real.log
                    (1 +
                      ((2 * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) / (m : ℝ)) * t) /
                        ((2 * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) / (m : ℝ)) +
                          (2 * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) / (m : ℝ)) *
                            bernoulliExpectation
                              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                              (fun Omega' =>
                                tangentSamplingDeviation Omega' S
                                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))))))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              TangentSamplingDeviationBound Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (bernoulliExpectation
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                    (fun Omega' =>
                      tangentSamplingDeviation Omega' S
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) +
                  tangentSamplingDeviationScale C β μ₀ (max n₁ n₂) r m)) ≥
          1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry

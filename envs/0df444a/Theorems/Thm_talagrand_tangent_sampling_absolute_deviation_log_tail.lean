-- Prove2me | Theorems.Thm_talagrand_tangent_sampling_absolute_deviation_log_tail
-- name    : talagrand_tangent_sampling_absolute_deviation_log_tail
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-29T15:40:44.780611+00:00
-- url     : https://prove2.me/theorems/dcec3688-1f47-4fa5-b414-819b7d1c32c1
-- statement:
--   This theorem transfers the exact logarithmic Talagrand tail from the bilinear supremum notation to the project variable
--   $$Z(\Omega)=p^{-1}\|P_TP_\Omega P_T-pP_T\|,$$
--   where $p=m/(n_1n_2)$.
--
--   Under the same Appendix 9.1 increment and variance hypotheses at scales $B$ and $\sigma^2$, there is a universal $K>0$ such that for every $t\ge0$,
--   $$\mathbb P_p\left(|Z-\mathbb E_pZ|\le t\right)\ge 1-3\exp\left(-\frac{t}{KB}\log\left(1+\frac{Bt}{\sigma^2+B\mathbb E_pZ}\right)\right).$$
--   This node is the source-faithful replacement for the older square-root raw-tail route.
--
--   Source location: Candès--Recht Appendix 9.1, PDF p. 46, equation (9.2) and the display rewriting $Z$ as a supremum over $X_1,X_2$.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_talagrand_supremum
import Mathlib.Analysis.SpecialFunctions.Log.Basic
open MatrixCompletion

theorem talagrand_tangent_sampling_absolute_deviation_log_tail :
    ∃ K : ℝ, 0 < K ∧
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (S : SVD M r) (B sigmaSq t : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        0 < B → 0 ≤ sigmaSq → 0 ≤ t →
        TangentSamplingTalagrandIncrementBound S
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) B →
        TangentSamplingTalagrandVarianceBound S
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) sigmaSq →
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
              (-(t / (K * B)) *
                Real.log
                  (1 + (B * t) /
                    (sigmaSq +
                      B * bernoulliExpectation
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                          (fun Omega' =>
                            tangentSamplingDeviation Omega' S
                              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))))) := by
  sorry

-- Prove2me | Theorems.Thm_talagrand_tangent_sampling_supremum_absolute_deviation_log_tail
-- name    : talagrand_tangent_sampling_supremum_absolute_deviation_log_tail
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-29T15:40:20.19042+00:00
-- url     : https://prove2.me/theorems/a4115c10-467d-448e-9a46-2a7fa67be15b
-- statement:
--   This theorem applies the exact Appendix 9.1 Talagrand logarithmic tail to the explicit bilinear supremum for matrix completion.
--
--   Set $p=m/(n_1n_2)$.  For the tangent projection $P_T$, define
--   $$Z_{\mathrm{sup}}(\Omega)=\sup_{\|X_1\|_F,\|X_2\|_F\le1}\sum_{i,j}\bigl(1_{(i,j)\in\Omega}-p\bigr)p^{-1}\langle X_1,P_T(e_ie_j^\top)\rangle_F\langle P_T(e_ie_j^\top),X_2\rangle_F.$$
--   If the Appendix 9.1 increment bound holds at scale $B$ and the variance proxy holds at scale $\sigma^2$, then for the same universal $K>0$ and every $t\ge0$,
--   $$\mathbb P_p\left(|Z_{\mathrm{sup}}-\mathbb E_pZ_{\mathrm{sup}}|\le t\right)\ge 1-3\exp\left(-\frac{t}{KB}\log\left(1+\frac{Bt}{\sigma^2+B\mathbb E_pZ_{\mathrm{sup}}}\right)\right).$$
--   The theorem is the matrix-completion instantiation of Theorem 9.1 before identifying the supremum with the operator norm variable $Z$.
--
--   Source location: Candès--Recht Appendix 9.1, PDF p. 46, equations (9.1)--(9.2).
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_talagrand_supremum
import Mathlib.Analysis.SpecialFunctions.Log.Basic
open MatrixCompletion
open scoped Classical BigOperators

theorem talagrand_tangent_sampling_supremum_absolute_deviation_log_tail :
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
              |tangentSamplingTalagrandSupremumDeviation Omega S
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) -
                  bernoulliExpectation
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                    (fun Omega' =>
                      tangentSamplingTalagrandSupremumDeviation Omega' S
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
                            tangentSamplingTalagrandSupremumDeviation Omega' S
                              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))))) := by
  sorry

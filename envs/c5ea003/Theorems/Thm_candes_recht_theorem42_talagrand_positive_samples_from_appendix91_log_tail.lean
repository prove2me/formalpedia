-- Prove2me | Theorems.Thm_candes_recht_theorem42_talagrand_positive_samples_from_appendix91_log_tail
-- name    : candes_recht_theorem42_talagrand_positive_samples_from_appendix91_log_tail
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-29T15:41:28.571719+00:00
-- url     : https://prove2.me/theorems/57f1e28d-6d82-4cff-917b-518d602cb39c
-- statement:
--   This is the positive-sample branch of the Talagrand part of Candès--Recht Theorem 4.2, following Appendix 9.1 exactly.
--
--   Let $n=\max(n_1,n_2)$ and $p=m/(n_1n_2)$ with $m>0$.  For
--   $$Z(\Omega)=p^{-1}\|P_TP_\Omega P_T-pP_T\|,$$
--   assume $A0(S,\mu_0)$ and the source proviso $\mathbb E_pZ\le1$.  If
--   $$m\ge C\mu_0nr\,\beta\log n,\qquad \beta>2,$$
--   then there are universal constants $C,c>0$ such that
--   $$\mathbb P_p\left(Z(\Omega)\le\mathbb E_pZ+C\sqrt{\frac{\mu_0nr\,\beta\log n}{m}}\right)\ge1-cn^{-\beta}.$$
--   The hypothesis $m>0$ is explicit because Appendix 9.1 uses $B=2\mu_0nr/m$.  The all-$m$ formal theorem is recovered by a separate zero-sample edge case.
--
--   Source location: Candès--Recht Theorem 4.2, PDF p. 19, equation (4.10), and Appendix 9.1, PDF pp. 46--47.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_talagrand
open MatrixCompletion

theorem candes_recht_theorem42_talagrand_positive_samples_from_appendix91_log_tail :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ C' : ℝ, C ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → 0 < m → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → A0 S μ₀ →
        (m : ℝ) ≥
          C' * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
            (β * Real.log (↑(max n₁ n₂))) →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              tangentSamplingDeviation Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤ 1 →
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

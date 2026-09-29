-- Prove2me | Theorems.Thm_candes_recht_theorem42_talagrand_deviation_around_mean_with_sample_constant
-- name    : candes_recht_theorem42_talagrand_deviation_around_mean_with_sample_constant
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-25T02:59:42.096636+00:00
-- url     : https://prove2.me/theorems/b87d54d2-3dde-4eee-b7f7-0a4b20e876ad
-- statement:
--   This is the Talagrand part of Candès--Recht Theorem 4.2, with the source proviso $\mathbb E_pZ\le1$ made explicit.
--
--   Let $n=\max(n_1,n_2)$ and $p=m/(n_1n_2)$.  For
--   $$Z(\Omega)=p^{-1}\|P_TP_\Omega P_T-pP_T\|,$$
--   assume the coherence hypothesis $A0(S,\mu_0)$ and
--   $$\mathbb E_pZ\le1.$$
--   If
--   $$m\ge C\mu_0nr\,\beta\log n,\qquad \beta>2,$$
--   then there are universal constants $C,c>0$ such that
--   $$\mathbb P_p\left(Z(\Omega)\le\mathbb E_pZ+C\sqrt{\frac{\mu_0nr\,\beta\log n}{m}}\right)\ge1-cn^{-\beta}.$$
--   The proof route uses Appendix 9.1 only when $m>0$, where $B=2\mu_0nr/m$ is meaningful; the formal $m=0$ edge case is handled separately by the sample lower bound.
--
--   Source location: Candès--Recht Theorem 4.2, PDF p. 19, equation (4.10), and Appendix 9.1, PDF pp. 46--47.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_talagrand
open MatrixCompletion

theorem candes_recht_theorem42_talagrand_deviation_around_mean_with_sample_constant :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ C' : ℝ, C ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
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

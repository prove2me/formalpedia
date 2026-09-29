-- Prove2me | Theorems.Thm_candes_recht_theorem42_tangent_sampling_deviation_bound_with_sample_constant
-- name    : candes_recht_theorem42_tangent_sampling_deviation_bound_with_sample_constant
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-25T02:51:41.313078+00:00
-- url     : https://prove2.me/theorems/d471f1e5-ecae-4038-bef9-5921a8dbd03a
-- statement:
--   This theorem is the Candes-Recht Theorem 4.2 tangent-sampling deviation estimate after the universal sample constant has been chosen large enough to satisfy the smallness provisos in the paper.
--
--   Let
--   $$
--   p=\frac{m}{n_1n_2},\qquad n=\max(n_1,n_2),\qquad
--   Z(\Omega)=p^{-1}\left\|P_TP_\Omega P_T-pP_T\right\|.
--   $$
--   Here $T$ is the tangent space determined by the singular-vector data $S$, and $A0(S,\mu_0)$ is the Candes-Recht coherence hypothesis controlling the tangent-space coordinate projections.
--
--   The theorem asserts that there are universal constants $C,c>0$ such that, for every larger sample constant $C'\ge C$ and every $\beta>2$, the lower bound
--   $$
--   m\ge C'\,\mu_0\,n\,r\,\beta\log n
--   $$
--   implies the high-probability deviation estimate
--   $$
--   \mathbb P_p\!\left(
--   Z(\Omega)\le C\sqrt{\frac{\mu_0 n r\,\beta\log n}{m}}
--   \right)\ge 1-c n^{-\beta}.
--   $$
--
--   This is not the under-specified Rudelson/Talagrand intermediate statement: the theorem deliberately packages the two paper provisos into the universal sample constant.  Equation (4.9) is used only when its right-hand side is below $1$, and equation (4.10) is applied under the hypothesis $\mathbb E Z\le 1$.
--
--   Source location: Candes-Recht 2008, PDF pp. 18--20, Theorem 4.2, equations (4.9)--(4.10), and the paragraph immediately following equation (4.10).
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem candes_recht_theorem42_tangent_sampling_deviation_bound_with_sample_constant :
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
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              TangentSamplingDeviationBound Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (tangentSamplingDeviationScale C β μ₀ (max n₁ n₂) r m)) ≥
          1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry

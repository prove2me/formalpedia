-- Prove2me | Theorems.Thm_candes_recht_theorem41_bernoulli_tangent_sampling_concentration
-- name    : candes_recht_theorem41_bernoulli_tangent_sampling_concentration
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-25T02:40:37.215324+00:00
-- url     : https://prove2.me/theorems/a703d451-9cb8-468c-9dbf-93e31b019fb8
-- statement:
--   This is Candes-Recht Theorem 4.1 in the Bernoulli sampling model, with the universal sample constant written as an explicit existential constant.
--
--   Let
--   $$
--   p=\frac{m}{n_1n_2},\qquad n=\max(n_1,n_2),
--   $$
--   and let $T$ be the tangent space determined by the singular-vector data $S$ of a rank-$r$ matrix $M$.  Assume the Candes-Recht incoherence hypothesis $A0(S,\mu_0)$, and sample each entry independently with probability $p$.
--
--   The theorem says that there are universal constants $C,c>0$ such that, for every larger constant $C'\ge C$ and every $\beta>2$, the sample lower bound
--   $$
--   m\ge C'\,\mu_0\,n\,r\,\beta\log n
--   $$
--   implies the tangent-space sampling operator is a $1/2$-contraction around its mean with probability at least $1-c n^{-\beta}$:
--   $$
--   \mathbb P_p\!\left(
--   \left\|p^{-1}P_TP_{\Omega}P_T-P_T\right\|\le \frac12
--   \right)\ge 1-c n^{-\beta}.
--   $$
--
--   This is the constant-reparameterized form of Candes-Recht Theorem 4.1.  The source proof uses Rudelson's expectation estimate, equation (4.9), Talagrand concentration, equation (4.10), and then chooses the universal sample constant large enough to satisfy the smallness proviso after equation (4.10).
--
--   Source location: Candes-Recht 2008, PDF pp. 18--20, Theorem 4.1 and equations (4.5), (4.9), (4.10).
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem candes_recht_theorem41_bernoulli_tangent_sampling_concentration :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ C' : ℝ, C ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          C' * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
            (β * Real.log (↑(max n₁ n₂))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              TangentSamplingConcentration Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) ((1 : ℝ) / 2)) ≥
          1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry

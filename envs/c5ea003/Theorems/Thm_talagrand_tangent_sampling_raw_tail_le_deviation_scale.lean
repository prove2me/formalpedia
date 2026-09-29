-- Prove2me | Theorems.Thm_talagrand_tangent_sampling_raw_tail_le_deviation_scale
-- name    : talagrand_tangent_sampling_raw_tail_le_deviation_scale
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-24T18:49:24.883166+00:00
-- url     : https://prove2.me/theorems/65e35cbd-d606-4b6b-a6f7-005920b5dc5d
-- statement:
--   This is the scalar conversion from the raw Talagrand radius to the standard Candes--Recht tangent-sampling deviation scale.
--
--   Appendix 9.1 supplies the common increment/variance scale
--   $$
--   B=\frac{2\mu_0 n r}{m},\qquad n=\max(n_1,n_2).
--   $$
--   For any fixed universal constant $K>0$, the theorem asserts that one can enlarge to another universal constant $C_{\rm tail}>0$ so that
--   $$
--   K\sqrt{B\,\beta\log n}
--   \le
--   C_{\rm tail}\sqrt{\frac{\mu_0 n r\,\beta\log n}{m}}
--   =
--   \operatorname{tangentSamplingDeviationScale}(C_{\rm tail},\beta,\mu_0,n,r,m).
--   $$
--
--   This node contains only scalar arithmetic and constant absorption; the probabilistic Talagrand inequality is isolated in the raw-tail child. Source location: Candes--Recht, PDF p. 19, equation (4.10), and Appendix 9.1.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_talagrand
open MatrixCompletion

theorem talagrand_tangent_sampling_raw_tail_le_deviation_scale
    (K : ℝ) :
    0 < K →
    ∃ Ctail : ℝ, 0 < Ctail ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (μ₀ : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r →
        1 ≤ μ₀ →
        K * Real.sqrt
            ((2 * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) / (m : ℝ)) *
              (β * Real.log (↑(max n₁ n₂)))) ≤
          tangentSamplingDeviationScale Ctail β μ₀ (max n₁ n₂) r m := by
  sorry

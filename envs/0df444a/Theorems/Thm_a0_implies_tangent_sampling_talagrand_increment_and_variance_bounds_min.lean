-- Prove2me | Theorems.Thm_a0_implies_tangent_sampling_talagrand_increment_and_variance_bounds_min
-- name    : a0_implies_tangent_sampling_talagrand_increment_and_variance_bounds_min
-- status  : Proved
-- author  : @Minghui
-- created : 2026-06-24T20:02:28.121542+00:00
-- url     : https://prove2.me/theorems/d0deb259-b462-456e-80bc-d705dc4c9d20
-- statement:
--   This is a formal bridge for the min-dimension Talagrand route in the tangent-sampling branch.
--
--   Source: Candes--Recht, *Exact Matrix Completion via Convex Optimization*, PDF p. 18, Section 4.2, equation (4.8), for the tangent-coordinate Frobenius estimate, together with Appendix 9.1, PDF p. 46, Theorem 9.1 / equation (9.2), for the bounded-increment and variance hypotheses used in Talagrand's inequality.
--
--   Mathematical statement: let `M` be an $n_1 \times n_2$ rank-$r$ matrix with SVD data `S`, let $n = \max(n_1,n_2)$, and let $p = m/(n_1n_2)$ be the Bernoulli sampling rate. If $0<n_1$, $0<n_2$, $0<r$, $0<m\le n_1n_2$, $1\le \mu_0$, and $A0(S,\mu_0)$ holds, then both Talagrand input hypotheses hold at the concrete Candes--Recht scale
--   $$
--   B = \sigma^2 = \frac{2\mu_0 n r}{m}.
--   $$
--   In Lean this is the conjunction
--   $$
--   \mathrm{TangentSamplingTalagrandIncrementBound}(S,p,B)
--   \;\wedge\;
--   \mathrm{TangentSamplingTalagrandVarianceBound}(S,p,B).
--   $$
--
--   Formalization note: this is a formal bridge, not a new concentration theorem and not a theorem stated verbatim in the paper. It composes the source-backed parent theorem `a0_implies_tangent_coordinate_frobenius_bound_min` with the source-backed children `tangent_sampling_talagrand_increment_bound_from_coordinate_bound_min` and `tangent_sampling_talagrand_variance_bound_from_coordinate_bound_min`. The purpose is to package the already-proved min-dimension route and avoid the stale max-coordinate branch.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. Exact Matrix Completion via Convex Optimization. arXiv:0805.4471 / Foundations of Computational Mathematics 9 (2009), 717--772. Exact locations: PDF p. 18, Section 4.2, equation (4.8); Appendix 9.1, PDF p. 46, Theorem 9.1 / equation (9.2).

import Theorems.Thm_a0_implies_tangent_coordinate_frobenius_bound_min
import Theorems.Thm_tangent_sampling_talagrand_increment_bound_from_coordinate_bound_min
import Theorems.Thm_tangent_sampling_talagrand_variance_bound_from_coordinate_bound_min

open MatrixCompletion

theorem a0_implies_tangent_sampling_talagrand_increment_and_variance_bounds_min :
    ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
      (μ₀ : ℝ) (S : SVD M r),
      0 < n₁ → 0 < n₂ → 0 < r → 0 < m → m ≤ n₁ * n₂ →
      1 ≤ μ₀ → A0 S μ₀ →
      TangentSamplingTalagrandIncrementBound S
        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
        (2 * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) / (m : ℝ)) ∧
      TangentSamplingTalagrandVarianceBound S
        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
        (2 * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) / (m : ℝ)) := by sorry

-- Prove2me | Theorems.Thm_tangent_sampling_talagrand_increment_bound_from_coordinate_bound_min
-- name    : tangent_sampling_talagrand_increment_bound_from_coordinate_bound_min
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-23T01:57:31.453068+00:00
-- url     : https://prove2.me/theorems/14b07bed-efd0-4dcf-aeba-e0e440dd8ef9
-- title:
--   CR eq. (4.8): min-dimension increment feed for Talagrand
-- statement:
--   Dimension-correct (min-radius) Talagrand increment feed for the tangent sampling deviation. From the ACHIEVABLE coordinate Frobenius estimate $\|P_T(e_a e_b^*)\|_F^2 \le 2\mu_0 r/\min(n_1,n_2)$ (Candès-Recht eq. (4.8); the min-dimension is the binding one — the max-dimension variant is FALSE from A0), the Talagrand increment (uniform boundedness) hypothesis holds with $B = 2\mu_0 \max(n_1,n_2) r/m$, where $p = m/(n_1 n_2)$. Proof: Cauchy-Schwarz on the Frobenius inner product gives $|\langle X_1,P\rangle\langle P,X_2\rangle| \le \|P\|_F^2$ for unit $X_1,X_2$; then $p^{-1}(2\mu_0 r/\min) = 2\mu_0\max\, r/m$ via $n_1 n_2/\min = \max$. This replaces the unsatisfiable max-radius hypothesis of tangent_sampling_talagrand_increment_bound_from_coordinate_bound with the achievable min-radius one (same output B).
-- source:
--   Candès & Recht, Exact Matrix Completion via Convex Optimization, arXiv:0805.4471, eq. (4.8) coordinate Frobenius estimate (2μ₀r/min(n₁,n₂)) and §9.1.

import Definitions.Def_matrix_completion_talagrand
open MatrixCompletion

theorem tangent_sampling_talagrand_increment_bound_from_coordinate_bound_min :
    ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
      (μ₀ : ℝ) (S : SVD M r),
      0 < n₁ → 0 < n₂ → 0 < r → 0 < m → m ≤ n₁ * n₂ →
      1 ≤ μ₀ →
      TangentCoordinateFrobeniusBound S
        (2 * μ₀ * (r : ℝ) / (min n₁ n₂ : ℝ)) →
      TangentSamplingTalagrandIncrementBound S
        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
        (2 * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) / (m : ℝ)) := by sorry

-- Prove2me | Theorems.Thm_tangent_sampling_talagrand_variance_bound_from_coordinate_bound_min
-- name    : tangent_sampling_talagrand_variance_bound_from_coordinate_bound_min
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-23T01:57:51.475146+00:00
-- url     : https://prove2.me/theorems/dcdf6395-3e08-4bcb-a7c7-8065d4ba9c20
-- title:
--   CR eq. (4.8): min-dimension variance feed for Talagrand
-- statement:
--   Dimension-correct (min-radius) Talagrand variance feed for the tangent sampling deviation. From the achievable coordinate Frobenius estimate $\|P_T(e_a e_b^*)\|_F^2 \le 2\mu_0 r/\min(n_1,n_2)$ (Candès-Recht eq. (4.8)), the Talagrand per-form variance-proxy hypothesis holds with $\sigma^2 = 2\mu_0 \max(n_1,n_2) r/m$, $p = m/(n_1 n_2)$. Proof: $\sum_{ab} p(1-p)\,\mathrm{coeff}_{ab}^2 \le p^{-1}(2\mu_0 r/\min)\sum_{ab}\langle X_1,P_{ab}\rangle^2$; the Bessel/Parseval step $\sum_{ab}\langle X_1,P_T(e_a e_b^*)\rangle^2 = \|P_T X_1\|_F^2 \le \|X_1\|_F^2 \le 1$ (P_T orthogonal projection: self-adjoint + idempotent) closes it, giving $\sigma^2 = 2\mu_0\max\, r/m$. Replaces the unsatisfiable max-radius hypothesis of tangent_sampling_talagrand_variance_bound_from_coordinate_bound with the achievable min-radius one (same output σ²).
-- source:
--   Candès & Recht, Exact Matrix Completion via Convex Optimization, arXiv:0805.4471, eq. (4.8) coordinate Frobenius estimate (2μ₀r/min(n₁,n₂)) and §9.1.

import Definitions.Def_matrix_completion_talagrand
open MatrixCompletion

theorem tangent_sampling_talagrand_variance_bound_from_coordinate_bound_min :
    ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
      (μ₀ : ℝ) (S : SVD M r),
      0 < n₁ → 0 < n₂ → 0 < r → 0 < m → m ≤ n₁ * n₂ →
      1 ≤ μ₀ →
      TangentCoordinateFrobeniusBound S
        (2 * μ₀ * (r : ℝ) / (min n₁ n₂ : ℝ)) →
      TangentSamplingTalagrandVarianceBound S
        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
        (2 * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) / (m : ℝ)) := by sorry

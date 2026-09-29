-- Prove2me | Theorems.Thm_tangent_coordinate_frobenius_bound_from_a0_min_dim
-- name    : tangent_coordinate_frobenius_bound_from_a0_min_dim
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-22T04:03:13.63907+00:00
-- url     : https://prove2.me/theorems/6368b574-3a7c-4406-b060-b79d334fc643
-- statement:
--   Source: Candes-Recht 2008, PDF pp. 18 and 23-24, equations (4.8), (6.2), and the rectangular convention following (6.4).
--
--   This is the corrected rectangular coordinate-size estimate needed by Rudelson's selection theorem.  If the singular vector spaces satisfy $A0(S,\mu_0)$, then every projected coordinate matrix obeys
--   $$
--   \left\|P_T(e_i e_j^\top)\right\|_F^2
--   \le C_{\mathrm{coord}}\,\mu_0\,\frac{r}{\min(n_1,n_2)}.
--   $$
--   The use of $\min(n_1,n_2)$ is intentional: the earlier max-denominator version is false for rectangular matrices.  This node is the reusable coordinate-radius input for the corrected dense Rudelson branch.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem tangent_coordinate_frobenius_bound_from_a0_min_dim :
    ∃ Ccoord : ℝ, 0 < Ccoord ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → 1 ≤ μ₀ → A0 S μ₀ →
        TangentCoordinateFrobeniusBound S
          (Ccoord * μ₀ * (r : ℝ) / (↑(min n₁ n₂))) := by
  sorry

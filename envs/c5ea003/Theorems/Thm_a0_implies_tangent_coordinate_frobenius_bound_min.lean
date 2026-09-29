-- Prove2me | Theorems.Thm_a0_implies_tangent_coordinate_frobenius_bound_min
-- name    : a0_implies_tangent_coordinate_frobenius_bound_min
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-06-21T04:58:41.295921+00:00
-- url     : https://prove2.me/theorems/2b86e79c-89e0-4f73-a572-aefebb07a996
-- statement:
--   Corrected Candès–Recht coordinate Frobenius estimate. Under the coherence assumption A0 (both column and row singular spaces have coherence at most $\mu_0$), every projected coordinate basis matrix satisfies $\|P_T(e_i e_j^\top)\|_F^2 \le \dfrac{2\mu_0 r}{\min(n_1,n_2)}$. This is the true estimate: writing $\alpha=\sum_k u_k(i)^2$ and $\gamma=\sum_\ell v_\ell(j)^2$, one has the exact identity $\|P_T(e_ie_j^\top)\|_F^2=\alpha+\gamma-\alpha\gamma\le\alpha+\gamma\le \mu_0 r/n_1+\mu_0 r/n_2\le 2\mu_0 r/\min(n_1,n_2)$. (This replaces the earlier $\max(n_1,n_2)$ form, which is false when $n_1\neq n_2$.)
-- source:
--   Candès, Recht, Exact Matrix Completion via Convex Optimization (2009), §3

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem a0_implies_tangent_coordinate_frobenius_bound_min {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r) (μ₀ : ℝ) : 0 < n₁ → 0 < n₂ → 0 < r → 1 ≤ μ₀ → A0 S μ₀ → TangentCoordinateFrobeniusBound S (2 * μ₀ * (r : ℝ) / (min n₁ n₂ : ℝ)) := by sorry

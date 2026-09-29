-- Prove2me | Theorems.Thm_quadratic_neumann_all_equal_base_entry_sup_norm_bound_geom_dim
-- name    : quadratic_neumann_all_equal_base_entry_sup_norm_bound_geom_dim
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-04T12:38:12.911577+00:00
-- url     : https://prove2.me/theorems/1a7caeb5-6a70-4206-b2bd-51b7f17156c8
-- statement:
--   Honest (geometric-mean) entrywise bound for the all-equal quadratic Neumann base matrix $B_\omega = E_\omega P_{\omega\omega}^2$ of CR08 eq. (6.21): under A0, $\|B\|_\infty \le C\,\mu_0^3 r^3/(\min(n_1,n_2)^2\sqrt{n_1n_2})$. The sign factor contributes $\mu_0 r/\sqrt{n_1n_2}$ (Cauchy-Schwarz from A0) and each diagonal kernel $P_{\omega\omega}=\langle P_T(e_ae_b^*),e_ae_b^*\rangle$ contributes $2\mu_0 r/\min(n_1,n_2)$ (eq. 4.8). This replaces the lossy $(r/\min)^3$ scale of quadratic_neumann_all_equal_base_entry_sup_norm_bound_min_dim, which is too weak to give the $\lambda^{-3/2}$ threshold in the rectangular regime $\min(n_1,n_2) \asymp \beta\log\max(n_1,n_2)$.
-- source:
--   Candes-Recht 2008, Exact Matrix Completion via Convex Optimization, Section 6.3 (proof of Lemma 4.6, all-equal case, eq. 6.21)

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_all_equal_base_entry_sup_norm_bound_geom_dim :
    ∃ Cbase : ℝ, 0 < Cbase ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → 1 ≤ μ₀ → A0 S μ₀ →
        entrySupNorm (quadraticNeumannAllEqualBaseMatrix S) ≤
          Cbase * μ₀ ^ 3 * (r : ℝ) ^ 3 /
            ((↑(min n₁ n₂)) ^ 2 * Real.sqrt ((n₁ : ℝ) * (n₂ : ℝ))) := by sorry

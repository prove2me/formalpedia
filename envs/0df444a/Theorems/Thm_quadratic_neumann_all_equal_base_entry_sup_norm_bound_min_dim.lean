-- Prove2me | Theorems.Thm_quadratic_neumann_all_equal_base_entry_sup_norm_bound_min_dim
-- name    : quadratic_neumann_all_equal_base_entry_sup_norm_bound_min_dim
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-21T15:11:30.57846+00:00
-- url     : https://prove2.me/theorems/55001c05-0921-4094-bcb0-cc9b3388cdfc
-- statement:
--   This is the corrected rectangular entrywise bound for the fixed all-equal quadratic base matrix in the proof of Lemma 4.6.
--
--   The all-equal quadratic term in Candes-Recht is expanded in equation (6.21). Its fixed base matrix has entries
--   $$
--   E_{\omega} P_{\omega\omega}^2 F_{\omega}.
--   $$
--   Using the A0 sign-entry bound and two copies of the A0 diagonal-kernel bound gives
--   $$
--   \left\|E_{\omega}P_{\omega\omega}^2F_{\omega}\right\|_\infty
--   \le C\,\mu_0^3\left({r\over \min(n_1,n_2)}\right)^3.
--   $$
--   Source: Candes-Recht 2008, PDF p. 23 estimates (6.2) and (6.4), PDF p. 24 rectangular-scale paragraph, and PDF p. 30 equation (6.21). This node replaces the older over-strong `max(n₁,n₂)` version.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_all_equal_base_entry_sup_norm_bound_min_dim :
    ∃ Cbase : ℝ, 0 < Cbase ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → 1 ≤ μ₀ → A0 S μ₀ →
        entrySupNorm (quadraticNeumannAllEqualBaseMatrix S) ≤
          Cbase * μ₀ ^ 3 *
            (((r : ℝ) / (↑(min n₁ n₂))) ^ 3) := by
  sorry

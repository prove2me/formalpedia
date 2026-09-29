-- Prove2me | Theorems.Thm_quadratic_neumann_all_equal_base_spectral_norm_bound_min_dim
-- name    : quadratic_neumann_all_equal_base_spectral_norm_bound_min_dim
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-21T15:51:04.33513+00:00
-- url     : https://prove2.me/theorems/a4fad7f4-92cf-4459-865d-5f280b25ab22
-- statement:
--   This is the source-corrected rectangular spectral norm bound for the all-equal quadratic base matrix in Lemma 4.6.
--
--   Equation (6.21) contains the fixed all-equal base matrix with entries
--   $$
--   E_\omega P_{\omega\omega}^2 F_\omega.
--   $$
--   Applying Lemma 6.4 twice, first to the sign matrix and then to the resulting diagonal multiplier, gives
--   $$
--   \left\|E_\omega P_{\omega\omega}^2F_\omega\right\|
--   \le C\left({\mu_0 r\over \min(n_1,n_2)}\right)^2.
--   $$
--   Source: Candes-Recht 2008, PDF p. 24 rectangular-scale paragraph, PDF p. 27 Lemma 6.4, and PDF p. 30 equation (6.21). This replaces the older over-strong $\max(n_1,n_2)$ denominator version.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_all_equal_base_spectral_norm_bound_min_dim :
    ∃ Cbase : ℝ, 0 < Cbase ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → 1 ≤ μ₀ → A0 S μ₀ →
        spectralNorm (quadraticNeumannAllEqualBaseMatrix S) ≤
          Cbase * ((μ₀ * (r : ℝ) / (↑(min n₁ n₂))) ^ 2) := by
  sorry

-- Prove2me | Theorems.Thm_linear_neumann_diagonal_base_entry_sup_norm_bound_min_dim
-- name    : linear_neumann_diagonal_base_entry_sup_norm_bound_min_dim
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-21T19:10:45.923039+00:00
-- url     : https://prove2.me/theorems/57fad37e-2802-48bd-a658-83963076259a
-- statement:
--   Rectangular-safe entry-sup estimate for the fixed diagonal base matrix in equation (6.9), now combining A0 and A1.
--
--   With $n=\max(n_1,n_2)$ and the rectangular tangent-kernel denominator $\min(n_1,n_2)$, the theorem states
--   $$
--   \|H\|_\infty
--   \le
--   C\,\mu_1\sqrt{\frac r{n_1n_2}}\,
--   \frac{\mu_0 r}{\min(n_1,n_2)}.
--   $$
--   Here $H$ is the fixed diagonal matrix $E_{ij}\langle P_T(e_i e_j^T),e_i e_j^T\rangle$ from the diagonal first-Neumann contribution.
--
--   Source: Candes-Recht 2008, PDF p. 23, estimate (6.2), PDF p. 26, equation (6.9), and Lemma 6.4/equations (6.10)--(6.11), combined with A1.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem linear_neumann_diagonal_base_entry_sup_norm_bound_min_dim :
    ∃ Cbase : ℝ, 0 < Cbase ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        entrySupNorm (linearNeumannDiagonalBaseMatrix S) ≤
          Cbase * μ₁ *
            Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) := by
  sorry

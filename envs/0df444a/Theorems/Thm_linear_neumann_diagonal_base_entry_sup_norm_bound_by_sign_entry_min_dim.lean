-- Prove2me | Theorems.Thm_linear_neumann_diagonal_base_entry_sup_norm_bound_by_sign_entry_min_dim
-- name    : linear_neumann_diagonal_base_entry_sup_norm_bound_by_sign_entry_min_dim
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-21T19:09:23.480079+00:00
-- url     : https://prove2.me/theorems/f0d2f1eb-15fc-46a0-9c41-5d9fabdbcf14
-- statement:
--   Rectangular-safe factored entry-sup estimate for the diagonal base matrix in the first Neumann correction.
--
--   Let
--   $$
--   H_{ij}=E_{ij}\,\langle P_T(e_i e_j^T),e_i e_j^T\rangle
--   $$
--   be the fixed diagonal coefficient matrix appearing in the decomposition of the diagonal contribution $S_0$ in equation (6.9).  Under $A0(S,\mu_0)$, the diagonal tangent-coordinate kernel is bounded at scale
--   $$
--   \mu_0 r / \min(n_1,n_2).
--   $$
--   Consequently
--   $$
--   \|H\|_\infty \le C\,{\mu_0 r\over \min(n_1,n_2)}\,\|E\|_\infty.
--   $$
--
--   Source: Candes-Recht 2008, PDF p. 23, estimate (6.2), PDF p. 26, equation (6.9), and Lemma 6.4/equations (6.10)--(6.11).
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem linear_neumann_diagonal_base_entry_sup_norm_bound_by_sign_entry_min_dim :
    ∃ Cbase : ℝ, 0 < Cbase ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → 1 ≤ μ₀ → A0 S μ₀ →
        entrySupNorm (linearNeumannDiagonalBaseMatrix S) ≤
          Cbase * μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) *
            entrySupNorm (signMatrix S) := by
  sorry

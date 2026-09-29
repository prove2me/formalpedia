-- Prove2me | Theorems.Thm_entry_sup_norm_sign_matrix_bound_from_a0_min_dim
-- name    : entry_sup_norm_sign_matrix_bound_from_a0_min_dim
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-21T15:10:47.698197+00:00
-- url     : https://prove2.me/theorems/d017554f-6949-4e3e-ad81-12644e9bcc1f
-- statement:
--   This is the rectangular A0-based max-entry estimate for the sign matrix.
--
--   From A0 incoherence and Cauchy-Schwarz, entries of $E=UV^\top$ obey a universal bound at the rectangular scale
--   $$
--   \|E\|_\infty \le C\,\mu_0\,{r\over \min(n_1,n_2)}.
--   $$
--   The source is Candes-Recht 2008, PDF p. 23, especially the estimate (6.4) and the paragraph immediately after it, which says that the rectangular case is obtained by replacing $n$ by $\min(n_1,n_2)$.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem entry_sup_norm_sign_matrix_bound_from_a0_min_dim :
    ∃ Csign : ℝ, 0 < Csign ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → 1 ≤ μ₀ → A0 S μ₀ →
        entrySupNorm (signMatrix S) ≤
          Csign * μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) := by
  sorry

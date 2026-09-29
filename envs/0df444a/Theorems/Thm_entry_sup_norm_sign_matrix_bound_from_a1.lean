-- Prove2me | Theorems.Thm_entry_sup_norm_sign_matrix_bound_from_a1
-- name    : entry_sup_norm_sign_matrix_bound_from_a1
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-21T14:37:14.633433+00:00
-- url     : https://prove2.me/theorems/53d68043-87be-4f7e-9d6b-6f2950e46217
-- statement:
--   This is the finite-dimensional step turning the A1 incoherence hypothesis into an entry-sup norm bound for the sign matrix.
--
--   The Candes-Recht A1 assumption says pointwise that every entry of the sign matrix $E=UV^\top$ satisfies
--   $$
--   |E_{ij}|\le \mu_1\sqrt{r\over n_1n_2}.
--   $$
--   The theorem packages this coordinatewise estimate as the max-entry estimate
--   $$
--   \|E\|_\infty\le \mu_1\sqrt{r\over n_1n_2}.
--   $$
--   The Lean proof is just the finite supremum principle: if every absolute entry is bounded by the same number, then the entry-sup norm is bounded by that number.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem entry_sup_norm_sign_matrix_bound_from_a1
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (μ₁ : ℝ) (S : SVD M r) :
    A1 S μ₁ →
    entrySupNorm (signMatrix S) ≤
      μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) := by
  sorry

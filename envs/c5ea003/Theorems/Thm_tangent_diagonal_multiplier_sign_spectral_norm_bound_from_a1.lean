-- Prove2me | Theorems.Thm_tangent_diagonal_multiplier_sign_spectral_norm_bound_from_a1
-- name    : tangent_diagonal_multiplier_sign_spectral_norm_bound_from_a1
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-23T15:58:43.834817+00:00
-- url     : https://prove2.me/theorems/57770761-02cb-488c-856d-6ea52d424d1e
-- statement:
--   This is the A1-effective form of the diagonal tangent-kernel multiplier estimate used for the deterministic mean term in Lemma 4.5.
--
--   For a matrix $X$, write
--   $$
--   D_T(X)_{ij}=X_{ij}\,\langle P_T(e_i e_j^\top),e_i e_j^\top\rangle.
--   $$
--   Specialized to the sign matrix $E=UV^\top$, A1 gives the sharper effective coordinate-energy scale $\mu_1^2$ for the actual singular-vector energies.  Hence there is a universal constant $C$ such that
--   $$
--   \|D_T(E)\|\le C {\mu_1^2 r\over \min(n_1,n_2)}\,\|E\|.
--   $$
--
--   Source: Candes-Recht 2008, PDF p. 4, assumption A1, and PDF p. 27, Lemma 6.4, equations (6.10)--(6.11); PDF p. 24 states that rectangular estimates replace $n$ by $\min(n_1,n_2)$.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem tangent_diagonal_multiplier_sign_spectral_norm_bound_from_a1 :
    ∃ Cdiag : ℝ, 0 < Cdiag ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → 1 ≤ μ₁ → A1 S μ₁ →
        spectralNorm (tangentDiagonalMultiplier S (signMatrix S)) ≤
          Cdiag * (μ₁ ^ 2 * (r : ℝ) / (↑(min n₁ n₂))) *
            spectralNorm (signMatrix S) := by
  sorry

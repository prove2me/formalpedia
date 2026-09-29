-- Prove2me | Theorems.Thm_tangent_diagonal_multiplier_spectral_norm_bound_min_dim
-- name    : tangent_diagonal_multiplier_spectral_norm_bound_min_dim
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-21T15:50:42.593497+00:00
-- url     : https://prove2.me/theorems/47ac7371-bbe2-44fd-8d8f-21df857ac32a
-- statement:
--   This is the rectangular version of Candes-Recht Lemma 6.4 for the diagonal tangent-kernel multiplier.
--
--   For a fixed matrix $X$, set
--   $$
--   D_T(X)_{ij}=X_{ij}\,\langle P_T(e_i e_j^\top),e_i e_j^\top\rangle.
--   $$
--   Under A0 incoherence of the rank-$r$ matrix, the theorem asserts that a universal constant $C$ satisfies
--   $$
--   \|D_T(X)\|\le C {\mu_0 r\over \min(n_1,n_2)}\|X\|
--   $$
--   for every fixed input matrix $X$.
--
--   The reduction separates Lemma 6.4 into three ingredients: A0 gives the coordinate-energy bounds, orthonormality gives the Bessel bounds by $1$, and the core multiplier estimate proves the operator-norm bound from the identity
--   $$
--   D_T(X)=\Lambda_U X(I-\Lambda_V)+X\Lambda_V.
--   $$
--
--   Source: Candes-Recht 2008, PDF p. 27, Lemma 6.4, equations (6.10)--(6.11); PDF p. 24 states that rectangular estimates replace $n$ by $\min(n_1,n_2)$.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem tangent_diagonal_multiplier_spectral_norm_bound_min_dim :
    ∃ Cdiag : ℝ, 0 < Cdiag ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → 1 ≤ μ₀ → A0 S μ₀ →
        spectralNorm (tangentDiagonalMultiplier S X) ≤
          Cdiag * (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) *
            spectralNorm X := by
  sorry

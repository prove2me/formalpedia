-- Prove2me | Theorems.Thm_tangent_projection_spectral_norm_le_universal_multiple
-- name    : tangent_projection_spectral_norm_le_universal_multiple
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-22T00:28:04.058861+00:00
-- url     : https://prove2.me/theorems/3be8590a-03c9-4f7e-8b99-e84be19e3f3c
-- statement:
--   This theorem states that the tangent-space projection $P_T$ has universally bounded operator norm for the matrix spectral norm.
--
--   Using the singular-space projections $P_U$ and $P_V$,
--   $$
--   P_T(X)=P_UX+XP_V-P_UXP_V=P_UX+(I-P_U)XP_V.
--   $$
--   The two summands are spectral-norm contractions, so
--   $$
--   \|P_T(X)\|\le 2\|X\|.
--   $$
--   The formal theorem only asks for some universal positive constant $C_T$.
--
--   Source: Candes-Recht 2008, PDF p. 15, Section 3, equation (3.5).
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem tangent_projection_spectral_norm_le_universal_multiple :
    ∃ Ctangent : ℝ, 0 < Ctangent ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (S : SVD M r) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        spectralNorm (tangentProjection S X) ≤ Ctangent * spectralNorm X := by
  sorry

-- Prove2me | Theorems.Thm_singular_projection_inclusion_exclusion_spectral_norm_le_original
-- name    : singular_projection_inclusion_exclusion_spectral_norm_le_original
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-22T00:12:16.550413+00:00
-- url     : https://prove2.me/theorems/7898c9b3-e0a7-47d7-9646-5f35cfeb08ad
-- statement:
--   This is the operator-norm contraction of the two-sided orthogonal complement projection.
--
--   For every matrix $X$,
--   $$
--   \|(I-P_U)X(I-P_V)\|\le \|X\|.
--   $$
--   Written in the Lean inclusion-exclusion notation, the left-hand side is
--   $$
--   \|X-P_UX-XP_V+P_UXP_V\|.
--   $$
--   The mathematical reason is that $I-P_U$ and $I-P_V$ are orthogonal projections, hence have operator norm at most $1$, and the matrix operator norm is submultiplicative.
--
--   Source: Candes-Recht 2008, PDF p. 24, Section 6.1, immediately before equation (6.5), where the proof uses $\|P_{T^\perp}(X)\|\le\|X\|$.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem singular_projection_inclusion_exclusion_spectral_norm_le_original
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    spectralNorm
        (X - leftSingularProjection S X - rightSingularProjection S X +
          twoSidedSingularProjection S X) ≤
      spectralNorm X := by
  sorry

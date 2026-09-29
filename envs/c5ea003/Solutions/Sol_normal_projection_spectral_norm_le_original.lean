-- Prove2me | solution 1 for normal_projection_spectral_norm_le_original
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-22T00:12:18.512904+00:00
-- url     : https://prove2.me/submissions/0568a415-bd7b-413d-a2fa-f34b19b02595

import Theorems.Thm_normal_projection_eq_inclusion_exclusion_of_singular_projections
import Theorems.Thm_singular_projection_inclusion_exclusion_spectral_norm_le_original

open MatrixCompletion

/-!
Source: Candes-Recht 2008, Section 3, PDF p. 15, equation (3.5), identifies
`T^\perp` with the two-sided orthogonal complement of the column and row
singular-vector spaces.  Section 6.1, PDF p. 24, immediately before equation
(6.5), uses the resulting contraction `||P_{T^\perp}(X)|| <= ||X||`.

Reduction: first rewrite the Lean definition of `normalProjection` into the
inclusion-exclusion operator `(I-P_U)X(I-P_V) = X-P_UX-XP_V+P_UXP_V`.  Then use
the spectral-norm contraction of left and right multiplication by the orthogonal
complement projectors.
-/

theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    spectralNorm (normalProjection S X) ≤ spectralNorm X := by
  rw [normal_projection_eq_inclusion_exclusion_of_singular_projections]
  exact singular_projection_inclusion_exclusion_spectral_norm_le_original S X

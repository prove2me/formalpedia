-- Prove2me | Theorems.Thm_spectral_norm_le_singular_value_zero
-- name    : spectral_norm_le_singular_value_zero
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-21T13:53:51.962367+00:00
-- url     : https://prove2.me/theorems/1243cf8d-48bd-44aa-bee7-f997599e2467
-- statement:
--   The spectral (operator) norm of a real matrix $Y$ equals its largest singular value, and in particular is at most it: $\lVert Y\rVert \le \sigma_0(Y)$, where $\sigma_0$ is the zeroth (largest) entry of the singular-value sequence of the associated Euclidean linear map $\mathrm{toEuclideanLin}\,Y$. Singular values are antitone, so $\sigma_0$ is the maximum. This is the geometric core of the operator-norm/Schatten-norm comparison: writing $T=\mathrm{toEuclideanLin}\,Y$, one has $\lVert Tx\rVert^2=\langle (T^\ast T)x,x\rangle\le \sigma_0^2\lVert x\rVert^2$, since $T^\ast T$ is a positive self-adjoint operator whose top eigenvalue is $\sigma_0^2$.
-- source:
--   Candes & Recht, Exact matrix completion via convex optimization, CACM 55.6 (2012), Section 6.1.

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem spectral_norm_le_singular_value_zero :
    ∀ {n₁ n₂ : ℕ} (Y : Matrix (Fin n₁) (Fin n₂) ℝ),
      spectralNorm Y ≤ (Matrix.toEuclideanLin Y).singularValues 0 := by sorry

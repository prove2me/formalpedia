-- Prove2me | Theorems.Thm_spectral_norm_eq_singular_value_zero
-- name    : spectral_norm_eq_singular_value_zero
-- status  : Proved
-- author  : @allychan327
-- created : 2026-06-23T17:44:43.44588+00:00
-- url     : https://prove2.me/theorems/12bcb7ca-65b7-46bc-8d6e-1b957c8c8d16
-- statement:
--   For any real matrix $Y$, its spectral (operator) norm equals its largest singular value, i.e. $\|Y\|_{op} = \sigma_1(Y) = (\mathrm{toEuclideanLin}\,Y).\mathrm{singularValues}\,0$. This is the standard identity (Horn & Johnson, *Matrix Analysis* 2nd ed., §5.6, and §7.3 on singular values) that the $\ell^2\to\ell^2$ operator norm of a matrix is its top singular value. Here `spectralNorm` is the operator norm of `Matrix.toEuclideanLin Y` and `singularValues 0` is the (sorted-descending) largest singular value. The equality combines the two inequality directions, both already proved on the platform (`spectral_norm_le_singular_value_zero` and `singular_value_zero_le_spectral_norm`), via antisymmetry. It is a reusable rewrite bridge between the operator-norm world and the singular-value world.
-- source:
--   Horn & Johnson, Matrix Analysis (2nd ed.), §5.6 (spectral norm = largest singular value) and §7.3 (singular value decomposition); Bhatia, Matrix Analysis, Prop. IV.2.4.

import Definitions.Def_matrix_completion_tangent
import Mathlib.Analysis.InnerProductSpace.SingularValues
open MatrixCompletion

theorem spectral_norm_eq_singular_value_zero :
    ∀ {n₁ n₂ : ℕ} (Y : Matrix (Fin n₁) (Fin n₂) ℝ),
      spectralNorm Y = (Matrix.toEuclideanLin Y).singularValues 0 := by sorry

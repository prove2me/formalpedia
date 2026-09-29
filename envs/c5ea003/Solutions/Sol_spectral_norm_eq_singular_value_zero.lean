-- Prove2me | solution 1 for spectral_norm_eq_singular_value_zero
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-06-23T17:45:17.497721+00:00
-- url     : https://prove2.me/submissions/910e07b3-9eda-4ae8-a5e4-fcf54f8c1b2c

import Theorems.Thm_spectral_norm_le_singular_value_zero
import Theorems.Thm_singular_value_zero_le_spectral_norm
import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem solution :
    ∀ {n₁ n₂ : ℕ} (Y : Matrix (Fin n₁) (Fin n₂) ℝ),
      spectralNorm Y = (Matrix.toEuclideanLin Y).singularValues 0 := by
  intro n₁ n₂ Y
  exact le_antisymm (spectral_norm_le_singular_value_zero Y)
    (singular_value_zero_le_spectral_norm Y)

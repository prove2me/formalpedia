-- Prove2me | Theorems.Thm_crouzeix_palencia_of_tendsto_auxiliary_bounds
-- name    : crouzeix_palencia_of_tendsto_auxiliary_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:51:25.176531+00:00
-- url     : https://prove2.me/theorems/09d7bf1f-ef59-4f41-80ca-8da8e11342cc
-- title:
--   crouzeix palencia of tendsto auxiliary bounds: crouzeix palencia of tendsto auxiliary bounds
-- statement:
--   Stagewise L4.2d/e bounds controlled by sequences converging to the target
--   polynomial sup norms imply the exact spectral-set conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PalenciaApproximation.lean#L90-L105
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PalenciaApproximation.lean#L90-L105

import Definitions.Def_Operator_Crouzeix_Palencia
import Definitions.Def_Operator_Crouzeix_PalenciaApproximation
set_option autoImplicit false
open Filter
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem crouzeix_palencia_of_tendsto_auxiliary_bounds
    (A : E →L[ℂ] E)
    (haux : ∀ p : Polynomial ℂ, ∃ M : ℕ → ℝ,
      Tendsto M atTop
          (nhds (polynomialSupNorm p (closure (numericalRange A)))) ∧
      ∀ n : ℕ, ∃ G : E →L[ℂ] E,
        ‖Polynomial.aeval A p + star G‖ ≤ 2 * M n ∧
        ‖Polynomial.aeval A p * G‖ ≤ (M n) ^ 2) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by sorry

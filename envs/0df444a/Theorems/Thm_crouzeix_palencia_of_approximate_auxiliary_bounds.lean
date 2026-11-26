-- Prove2me | Theorems.Thm_crouzeix_palencia_of_approximate_auxiliary_bounds
-- name    : crouzeix_palencia_of_approximate_auxiliary_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:36:58.506461+00:00
-- url     : https://prove2.me/theorems/2128dc41-5622-4bf1-8a0d-d2d34a0713d8
-- title:
--   crouzeix palencia of approximate auxiliary bounds: crouzeix palencia of approximate auxiliary bounds
-- statement:
--   Approximate L4.2d/e auxiliary bounds for every polynomial suffice for
--   the exact Crouzeix--Palencia polynomial spectral-set conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PalenciaApproximation.lean#L72-L86
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PalenciaApproximation.lean#L72-L86

import Definitions.Def_Operator_Crouzeix_Palencia
import Definitions.Def_Operator_Crouzeix_PalenciaApproximation
set_option autoImplicit false
open Filter
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem crouzeix_palencia_of_approximate_auxiliary_bounds
    (A : E →L[ℂ] E)
    (haux : ∀ (p : Polynomial ℂ) (ε : ℝ), 0 < ε →
      ∃ G : E →L[ℂ] E,
        ‖Polynomial.aeval A p + star G‖ ≤
            2 * (polynomialSupNorm p (closure (numericalRange A)) + ε) ∧
        ‖Polynomial.aeval A p * G‖ ≤
            (polynomialSupNorm p (closure (numericalRange A)) + ε) ^ 2) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by sorry

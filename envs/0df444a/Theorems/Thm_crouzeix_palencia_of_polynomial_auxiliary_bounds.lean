-- Prove2me | Theorems.Thm_crouzeix_palencia_of_polynomial_auxiliary_bounds
-- name    : crouzeix_palencia_of_polynomial_auxiliary_bounds
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:36:34.908359+00:00
-- url     : https://prove2.me/theorems/8b39940d-ef34-47ac-8ce3-94f9d483e9fc
-- title:
--   crouzeix palencia of polynomial auxiliary bounds: crouzeix palencia of polynomial auxiliary bounds
-- statement:
--   The L4.2d/e interface specialized to the contour operator from
--   `AuxOperator.lean`: once its symmetrized and product bounds hold for every
--   polynomial, the Crouzeix--Palencia spectral-set conclusion follows.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/Palencia.lean#L839-L849
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/Palencia.lean#L839-L849

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Normal
import Definitions.Def_Operator_Crouzeix_Palencia
set_option autoImplicit false
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]

theorem crouzeix_palencia_of_polynomial_auxiliary_bounds
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (hbounds : ∀ p : Polynomial ℂ,
      ‖Polynomial.aeval A p + star (crouzeixPolynomialAuxiliaryOperator A Omega p)‖ ≤
        2 * polynomialSupNorm p (closure (numericalRange A)) ∧
      ‖Polynomial.aeval A p * crouzeixPolynomialAuxiliaryOperator A Omega p‖ ≤
        polynomialSupNorm p (closure (numericalRange A)) ^ 2) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2) (closure (numericalRange A)) := by sorry

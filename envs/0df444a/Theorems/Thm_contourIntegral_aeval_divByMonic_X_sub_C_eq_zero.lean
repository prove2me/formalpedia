-- Prove2me | Theorems.Thm_contourIntegral_aeval_divByMonic_X_sub_C_eq_zero
-- name    : contourIntegral_aeval_divByMonic_X_sub_C_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:53:51.858003+00:00
-- url     : https://prove2.me/theorems/40e4bd83-de43-4179-92a6-bf12ba418e65
-- title:
--   contour Integral aeval div By Monic X sub C eq zero: contour Integral aeval div By Monic X sub C eq zero
-- statement:
--   The operator-valued divided difference
--   `z ↦ (p /ₘ (X - C z))(A)` has zero integral around every smooth closed
--   boundary.  Coefficient expansion makes it a finite sum of nonnegative powers
--   of `z`, each of which has a global polynomial primitive.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialCauchyFromResolventMass.lean#L94-L139
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialCauchyFromResolventMass.lean#L94-L139

import Definitions.Def_Operator_Crouzeix_ProductContour
import Definitions.Def_Operator_Crouzeix_PolynomialCauchyFromResolventMass
set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem contourIntegral_aeval_divByMonic_X_sub_C_eq_zero
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (p : Polynomial ℂ) :
    contourIntegral
        (fun z => Polynomial.aeval A
          (p /ₘ (Polynomial.X - Polynomial.C z)))
        Omega.boundaryParam = 0 := by sorry

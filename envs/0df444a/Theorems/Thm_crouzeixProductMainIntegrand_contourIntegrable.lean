-- Prove2me | Theorems.Thm_crouzeixProductMainIntegrand_contourIntegrable
-- name    : crouzeixProductMainIntegrand_contourIntegrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:43:02.076773+00:00
-- url     : https://prove2.me/theorems/025fdc8d-28f3-528b-9fd8-a4ca8651ed7a
-- title:
--   crouzeix Product Main Integrand contour Integrable: crouzeix Product Main Integrand contour Integrable
-- statement:
--   The scalar-square resolvent term in the Crouzeix--Palencia product
--   splitting is contour integrable on every smooth boundary containing the
--   closed numerical range.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductContour.lean#L152-L160
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductContour.lean#L152-L160

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Mathlib.Topology.Algebra.Polynomial
import Definitions.Def_Operator_Crouzeix_ProductContour
set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem crouzeixProductMainIntegrand_contourIntegrable [CompleteSpace E]
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier) :
    ContourIntegrable
      (fun z => (star (Polynomial.eval z p) * Polynomial.eval z p) •
        resolvent A z) Omega.boundaryParam := by sorry

-- Prove2me | Theorems.Thm_crouzeixProductRemainderIntegrand_contourIntegrable
-- name    : crouzeixProductRemainderIntegrand_contourIntegrable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:43:32.899942+00:00
-- url     : https://prove2.me/theorems/936d646f-b93e-4b86-8df2-9aaae86b5af1
-- title:
--   crouzeix Product Remainder Integrand contour Integrable: crouzeix Product Remainder Integrand contour Integrable
-- statement:
--   The polynomial divided-difference remainder in the
--   Crouzeix--Palencia product splitting is contour integrable on every smooth
--   boundary.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductContour.lean#L165-L175
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductContour.lean#L165-L175

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Mathlib.Topology.Algebra.Polynomial
import Definitions.Def_Operator_Crouzeix_ProductContour
set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem crouzeixProductRemainderIntegrand_contourIntegrable
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (p : Polynomial ℂ) :
    ContourIntegrable
      (fun z => star (Polynomial.eval z p) •
        Polynomial.aeval A (p /ₘ (Polynomial.X - Polynomial.C z)))
      Omega.boundaryParam := by sorry

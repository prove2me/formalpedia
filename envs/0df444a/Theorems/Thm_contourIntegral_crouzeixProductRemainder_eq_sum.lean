-- Prove2me | Theorems.Thm_contourIntegral_crouzeixProductRemainder_eq_sum
-- name    : contourIntegral_crouzeixProductRemainder_eq_sum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:43:14.319475+00:00
-- url     : https://prove2.me/theorems/0af76002-acbf-5c34-b2d0-11f8d60ceef8
-- title:
--   contour Integral crouzeix Product Remainder eq sum: contour Integral crouzeix Product Remainder eq sum
-- statement:
--   The divided-difference remainder contour is a finite sum of scalar
--   contour coefficients multiplying powers of `A`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductContour.lean#L179-L236
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductContour.lean#L179-L236

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Mathlib.Topology.Algebra.Polynomial
import Definitions.Def_Operator_Crouzeix_ProductContour
set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem contourIntegral_crouzeixProductRemainder_eq_sum [CompleteSpace E]
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (p : Polynomial ℂ) :
    contourIntegral
        (fun z => star (Polynomial.eval z p) •
          Polynomial.aeval A (p /ₘ (Polynomial.X - Polynomial.C z)))
        Omega.boundaryParam =
      ∑ i ∈ Finset.range p.natDegree,
        contourIntegral
          (fun z => star (Polynomial.eval z p) *
            (p /ₘ (Polynomial.X - Polynomial.C z)).coeff i)
          Omega.boundaryParam • A ^ i := by sorry

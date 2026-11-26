-- Prove2me | Theorems.Thm_normalized_contourIntegral_resolvent_eq_one_of_cauchy
-- name    : normalized_contourIntegral_resolvent_eq_one_of_cauchy
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:52:36.594795+00:00
-- url     : https://prove2.me/theorems/47bc1f4d-f559-55fa-abd1-948ff8809ab0
-- title:
--   normalized contour Integral resolvent eq one of cauchy: normalized contour Integral resolvent eq one of cauchy
-- statement:
--   A raw smooth-contour resolvent Cauchy identity becomes the identity
--   operator after multiplication by `(2πi)⁻¹`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductBase.lean#L52-L62
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductBase.lean#L52-L62

import Definitions.Def_Operator_Crouzeix_ProductContour
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Definitions.Def_Operator_Crouzeix_ProductBase
set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem normalized_contourIntegral_resolvent_eq_one_of_cauchy [CompleteSpace E]
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (hCauchy : contourIntegral (resolvent A) Omega.boundaryParam =
      (2 * (Real.pi : ℂ) * Complex.I) • (1 : E →L[ℂ] E)) :
    (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
        contourIntegral (resolvent A) Omega.boundaryParam = 1 := by sorry

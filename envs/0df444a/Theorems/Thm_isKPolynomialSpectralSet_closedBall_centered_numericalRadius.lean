-- Prove2me | Theorems.Thm_isKPolynomialSpectralSet_closedBall_centered_numericalRadius
-- name    : isKPolynomialSpectralSet_closedBall_centered_numericalRadius
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:45:29.755956+00:00
-- url     : https://prove2.me/theorems/1805e836-3431-52f7-aa54-9ba14aaeecf9
-- title:
--   is KPolynomial Spectral Set closed Ball centered numerical Radius: is KPolynomial Spectral Set closed Ball centered numerical Radius
-- statement:
--   The disk centered at `c` with radius `w(A-cI)` is a polynomial spectral
--   set with the Crouzeix--Palencia constant.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralSetSuperset.lean#L77-L83
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralSetSuperset.lean#L77-L83

import Definitions.Def_Operator_Crouzeix_NormalPolynomialBound
import Definitions.Def_Operator_Crouzeix_SpectralSetMonotone
import Definitions.Def_Operator_NumericalRange_RadiusAffine
import Definitions.Def_Operator_Crouzeix_SpectralSetSuperset
set_option autoImplicit false
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem isKPolynomialSpectralSet_closedBall_centered_numericalRadius
    (A : E →L[ℂ] E) (c : ℂ) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (Metric.closedBall c (numericalRadius (A - c • 1))) := by sorry

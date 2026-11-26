-- Prove2me | Theorems.Thm_isKPolynomialSpectralSet_closedBall_numericalRadius
-- name    : isKPolynomialSpectralSet_closedBall_numericalRadius
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:50:26.395111+00:00
-- url     : https://prove2.me/theorems/166eac36-28ae-4a66-b9c2-e5d991d7fe3b
-- title:
--   is KPolynomial Spectral Set closed Ball numerical Radius: is KPolynomial Spectral Set closed Ball numerical Radius
-- statement:
--   The closed disk centered at zero with radius `w(A)` is a polynomial
--   spectral set with the Crouzeix--Palencia constant.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralSetSuperset.lean#L38-L44
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralSetSuperset.lean#L38-L44

import Definitions.Def_Operator_Crouzeix_NormalPolynomialBound
import Definitions.Def_Operator_Crouzeix_SpectralSetMonotone
import Definitions.Def_Operator_NumericalRange_RadiusAffine
import Definitions.Def_Operator_Crouzeix_SpectralSetSuperset
set_option autoImplicit false
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem isKPolynomialSpectralSet_closedBall_numericalRadius
    (A : E →L[ℂ] E) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (Metric.closedBall 0 (numericalRadius A)) := by sorry

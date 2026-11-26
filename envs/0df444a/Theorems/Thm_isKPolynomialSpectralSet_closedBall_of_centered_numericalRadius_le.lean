-- Prove2me | Theorems.Thm_isKPolynomialSpectralSet_closedBall_of_centered_numericalRadius_le
-- name    : isKPolynomialSpectralSet_closedBall_of_centered_numericalRadius_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:49:53.943867+00:00
-- url     : https://prove2.me/theorems/c15a8152-b149-56cd-98b4-c9c2c57b4a62
-- title:
--   is KPolynomial Spectral Set closed Ball of centered numerical Radius le: is KPolynomial Spectral Set closed Ball of centered numerical Radius le
-- statement:
--   Every disk whose radius dominates `w(A-cI)` is a polynomial spectral set
--   with the Crouzeix--Palencia constant.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralSetSuperset.lean#L98-L104
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralSetSuperset.lean#L98-L104

import Definitions.Def_Operator_Crouzeix_NormalPolynomialBound
import Definitions.Def_Operator_Crouzeix_SpectralSetMonotone
import Definitions.Def_Operator_NumericalRange_RadiusAffine
import Definitions.Def_Operator_Crouzeix_SpectralSetSuperset
set_option autoImplicit false
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem isKPolynomialSpectralSet_closedBall_of_centered_numericalRadius_le
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ}
    (hR : numericalRadius (A - c • 1) ≤ R) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2) (Metric.closedBall c R) := by sorry

-- Prove2me | Theorems.Thm_isKPolynomialSpectralSet_closedBall_of_numericalRadius_le
-- name    : isKPolynomialSpectralSet_closedBall_of_numericalRadius_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:09:45.098891+00:00
-- url     : https://prove2.me/theorems/b9a202b3-c032-5319-a774-7d5dcae38950
-- title:
--   is KPolynomial Spectral Set closed Ball of numerical Radius le: is KPolynomial Spectral Set closed Ball of numerical Radius le
-- statement:
--   Every centered closed disk whose radius dominates `w(A)` is a polynomial
--   spectral set with the Crouzeix--Palencia constant.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralSetSuperset.lean#L58-L64
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralSetSuperset.lean#L58-L64

import Definitions.Def_Operator_Crouzeix_NormalPolynomialBound
import Definitions.Def_Operator_Crouzeix_SpectralSetMonotone
import Definitions.Def_Operator_NumericalRange_RadiusAffine
import Definitions.Def_Operator_Crouzeix_SpectralSetSuperset
set_option autoImplicit false
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem isKPolynomialSpectralSet_closedBall_of_numericalRadius_le
    (A : E →L[ℂ] E) {R : ℝ} (hR : numericalRadius A ≤ R) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (Metric.closedBall 0 R) := by sorry

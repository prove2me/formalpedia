-- Prove2me | Theorems.Thm_isPolynomialSpectralSet_closedBall_of_isStarNormal_of_numericalRadius_le
-- name    : isPolynomialSpectralSet_closedBall_of_isStarNormal_of_numericalRadius_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:09:48.45666+00:00
-- url     : https://prove2.me/theorems/15c3b0f0-1543-5c4d-9c54-a7d6ee7bd5ce
-- title:
--   is Polynomial Spectral Set closed Ball of is Star Normal of numerical Radius le: is Polynomial Spectral Set closed Ball of is Star Normal of numerical Radius le
-- statement:
--   For a normal operator, every centered closed disk whose radius dominates
--   `w(A)` is a constant-one polynomial spectral set.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralSetSuperset.lean#L68-L73
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralSetSuperset.lean#L68-L73

import Definitions.Def_Operator_Crouzeix_NormalPolynomialBound
import Definitions.Def_Operator_Crouzeix_SpectralSetMonotone
import Definitions.Def_Operator_NumericalRange_RadiusAffine
import Definitions.Def_Operator_Crouzeix_SpectralSetSuperset
set_option autoImplicit false
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem isPolynomialSpectralSet_closedBall_of_isStarNormal_of_numericalRadius_le
    (A : E →L[ℂ] E) [IsStarNormal A] {R : ℝ}
    (hR : numericalRadius A ≤ R) :
    IsPolynomialSpectralSet A (Metric.closedBall 0 R) := by sorry

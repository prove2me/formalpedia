-- Prove2me | Theorems.Thm_isPolynomialSpectralSet_closedBall_of_isStarNormal_of_centered_numericalRadius_le
-- name    : isPolynomialSpectralSet_closedBall_of_isStarNormal_of_centered_numericalRadius_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:50:33.69514+00:00
-- url     : https://prove2.me/theorems/3e69b6bf-5170-493d-afce-f939a6a55df6
-- title:
--   is Polynomial Spectral Set closed Ball of is Star Normal of centered numerical Radius le: is Polynomial Spectral Set closed Ball of is Star Normal of centered numerical Radius le
-- statement:
--   For a normal operator, every disk whose radius dominates `w(A-cI)` is a
--   constant-one polynomial spectral set.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralSetSuperset.lean#L108-L115
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralSetSuperset.lean#L108-L115

import Definitions.Def_Operator_Crouzeix_NormalPolynomialBound
import Definitions.Def_Operator_Crouzeix_SpectralSetMonotone
import Definitions.Def_Operator_NumericalRange_RadiusAffine
import Definitions.Def_Operator_Crouzeix_SpectralSetSuperset
set_option autoImplicit false
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem isPolynomialSpectralSet_closedBall_of_isStarNormal_of_centered_numericalRadius_le
    (A : E →L[ℂ] E) [IsStarNormal A] (c : ℂ) {R : ℝ}
    (hR : numericalRadius (A - c • 1) ≤ R) :
    IsPolynomialSpectralSet A (Metric.closedBall c R) := by sorry

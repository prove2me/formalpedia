-- Prove2me | Theorems.Thm_isPolynomialSpectralSet_closedBall_centered_numericalRadius_of_isStarNormal
-- name    : isPolynomialSpectralSet_closedBall_centered_numericalRadius_of_isStarNormal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:45:45.569052+00:00
-- url     : https://prove2.me/theorems/7c0da125-823c-5826-bd20-39334ac7c9f2
-- title:
--   is Polynomial Spectral Set closed Ball centered numerical Radius of is Star Normal: is Polynomial Spectral Set closed Ball centered numerical Radius of is Star Normal
-- statement:
--   For a normal operator, the disk centered at `c` with radius `w(A-cI)` is
--   a constant-one polynomial spectral set.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralSetSuperset.lean#L87-L94
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralSetSuperset.lean#L87-L94

import Definitions.Def_Operator_Crouzeix_NormalPolynomialBound
import Definitions.Def_Operator_Crouzeix_SpectralSetMonotone
import Definitions.Def_Operator_NumericalRange_RadiusAffine
import Definitions.Def_Operator_Crouzeix_SpectralSetSuperset
set_option autoImplicit false
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem isPolynomialSpectralSet_closedBall_centered_numericalRadius_of_isStarNormal
    (A : E →L[ℂ] E) [IsStarNormal A] (c : ℂ) :
    IsPolynomialSpectralSet A
      (Metric.closedBall c (numericalRadius (A - c • 1))) := by sorry

-- Prove2me | Theorems.Thm_isPolynomialSpectralSet_closedBall_numericalRadius_of_isStarNormal
-- name    : isPolynomialSpectralSet_closedBall_numericalRadius_of_isStarNormal
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:49:45.94083+00:00
-- url     : https://prove2.me/theorems/ef38fcc7-4644-50fd-84f1-1ba5e6d06615
-- title:
--   is Polynomial Spectral Set closed Ball numerical Radius of is Star Normal: is Polynomial Spectral Set closed Ball numerical Radius of is Star Normal
-- statement:
--   For a normal operator, the numerical-radius disk is a constant-one
--   polynomial spectral set.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralSetSuperset.lean#L48-L54
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralSetSuperset.lean#L48-L54

import Definitions.Def_Operator_Crouzeix_NormalPolynomialBound
import Definitions.Def_Operator_Crouzeix_SpectralSetMonotone
import Definitions.Def_Operator_NumericalRange_RadiusAffine
import Definitions.Def_Operator_Crouzeix_SpectralSetSuperset
set_option autoImplicit false
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem isPolynomialSpectralSet_closedBall_numericalRadius_of_isStarNormal
    (A : E →L[ℂ] E) [IsStarNormal A] :
    IsPolynomialSpectralSet A
      (Metric.closedBall 0 (numericalRadius A)) := by sorry

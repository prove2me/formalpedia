-- Prove2me | Theorems.Thm_exists_minimal_centered_numericalRadius_isPolynomialSpectralSet_of_isStarNormal
-- name    : exists_minimal_centered_numericalRadius_isPolynomialSpectralSet_of_isStarNormal
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:14:17.032803+00:00
-- url     : https://prove2.me/theorems/39661316-47e5-51e0-acf7-468ae40849e0
-- title:
--   exists minimal centered numerical Radius is Polynomial Spectral Set of is Star Normal: exists minimal centered numerical Radius is Polynomial Spectral Set of is Star Normal
-- statement:
--   For a normal operator, a globally minimal centered numerical-radius disk
--   is a constant-one polynomial spectral set.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralSetSuperset.lean#L154-L164
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralSetSuperset.lean#L154-L164

import Definitions.Def_Operator_Crouzeix_NormalPolynomialBound
import Definitions.Def_Operator_Crouzeix_SpectralSetMonotone
import Definitions.Def_Operator_NumericalRange_RadiusAffine
import Definitions.Def_Operator_Crouzeix_SpectralSetSuperset
set_option autoImplicit false
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem exists_minimal_centered_numericalRadius_isPolynomialSpectralSet_of_isStarNormal
    [Nontrivial E] (A : E →L[ℂ] E) [IsStarNormal A] :
    ∃ c : ℂ,
      (∀ d : ℂ,
        numericalRadius (A - c • 1) ≤ numericalRadius (A - d • 1)) ∧
      IsPolynomialSpectralSet A
        (Metric.closedBall c (numericalRadius (A - c • 1))) := by sorry

-- Prove2me | Theorems.Thm_exists_minimal_centered_numericalRadius_isKPolynomialSpectralSet
-- name    : exists_minimal_centered_numericalRadius_isKPolynomialSpectralSet
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:14:00.975531+00:00
-- url     : https://prove2.me/theorems/b910e7db-6dd6-5c42-be64-313b650990eb
-- title:
--   exists minimal centered numerical Radius is KPolynomial Spectral Set: exists minimal centered numerical Radius is KPolynomial Spectral Set
-- statement:
--   A nontrivial Hilbert space admits a globally minimal centered
--   numerical-radius disk, and that disk is a polynomial spectral set with the
--   Crouzeix--Palencia constant.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralSetSuperset.lean#L142-L150
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralSetSuperset.lean#L142-L150

import Definitions.Def_Operator_Crouzeix_NormalPolynomialBound
import Definitions.Def_Operator_Crouzeix_SpectralSetMonotone
import Definitions.Def_Operator_NumericalRange_RadiusAffine
import Definitions.Def_Operator_Crouzeix_SpectralSetSuperset
set_option autoImplicit false
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem exists_minimal_centered_numericalRadius_isKPolynomialSpectralSet
    [Nontrivial E] (A : E →L[ℂ] E) :
    ∃ c : ℂ,
      (∀ d : ℂ,
        numericalRadius (A - c • 1) ≤ numericalRadius (A - d • 1)) ∧
      IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
        (Metric.closedBall c (numericalRadius (A - c • 1))) := by sorry

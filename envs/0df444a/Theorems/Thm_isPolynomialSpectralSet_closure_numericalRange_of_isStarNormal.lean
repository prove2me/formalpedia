-- Prove2me | Theorems.Thm_isPolynomialSpectralSet_closure_numericalRange_of_isStarNormal
-- name    : isPolynomialSpectralSet_closure_numericalRange_of_isStarNormal
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:47:22.215467+00:00
-- url     : https://prove2.me/theorems/27a3b1bb-59b1-5b94-9bb4-b7408d3a9731
-- title:
--   is Polynomial Spectral Set closure numerical Range of is Star Normal: is Polynomial Spectral Set closure numerical Range of is Star Normal
-- statement:
--   The closed numerical range is a polynomial spectral set with sharp
--   constant `1` for every normal operator.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalPolynomialBound.lean#L23-L32
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalPolynomialBound.lean#L23-L32

import Definitions.Def_Operator_Crouzeix_PolynomialBound
import Definitions.Def_Operator_NumericalRange_RadiusNormal
import Definitions.Def_Operator_SpectralSet_Normal
import Definitions.Def_Operator_Crouzeix_NormalPolynomialBound
set_option autoImplicit false
open Complex Set
open scoped InnerProductSpace Polynomial
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem isPolynomialSpectralSet_closure_numericalRange_of_isStarNormal
    (A : E →L[ℂ] E) [IsStarNormal A] :
    IsPolynomialSpectralSet A (closure (numericalRange A)) := by sorry

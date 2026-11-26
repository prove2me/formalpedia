-- Prove2me | Theorems.Thm_isPolynomialSpectralSet_of_isStarNormal_of_closure_numericalRange_subset
-- name    : isPolynomialSpectralSet_of_isStarNormal_of_closure_numericalRange_subset
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:45:45.803112+00:00
-- url     : https://prove2.me/theorems/c976dd8c-794b-41c6-9917-4684fff62593
-- title:
--   is Polynomial Spectral Set of is Star Normal of closure numerical Range subset: is Polynomial Spectral Set of is Star Normal of closure numerical Range subset
-- statement:
--   For a normal operator, every compact superset of the closed numerical
--   range is a constant-one polynomial spectral set.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralSetSuperset.lean#L28-L34
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralSetSuperset.lean#L28-L34

import Definitions.Def_Operator_Crouzeix_NormalPolynomialBound
import Definitions.Def_Operator_Crouzeix_SpectralSetMonotone
import Definitions.Def_Operator_NumericalRange_RadiusAffine
import Definitions.Def_Operator_Crouzeix_SpectralSetSuperset
set_option autoImplicit false
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem isPolynomialSpectralSet_of_isStarNormal_of_closure_numericalRange_subset
    (A : E →L[ℂ] E) [IsStarNormal A]
    {K : Set ℂ} (hK : IsCompact K)
    (hsub : closure (numericalRange A) ⊆ K) :
    IsPolynomialSpectralSet A K := by sorry

-- Prove2me | Theorems.Thm_isKPolynomialSpectralSet_of_closure_numericalRange_subset
-- name    : isKPolynomialSpectralSet_of_closure_numericalRange_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:45:16.748012+00:00
-- url     : https://prove2.me/theorems/477ba090-96e7-5a30-836f-e27a9bcf8496
-- title:
--   is KPolynomial Spectral Set of closure numerical Range subset: is KPolynomial Spectral Set of closure numerical Range subset
-- statement:
--   Every compact superset of the closed numerical range is a polynomial
--   spectral set with the Crouzeix--Palencia constant.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralSetSuperset.lean#L20-L24
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralSetSuperset.lean#L20-L24

import Definitions.Def_Operator_Crouzeix_NormalPolynomialBound
import Definitions.Def_Operator_Crouzeix_SpectralSetMonotone
import Definitions.Def_Operator_NumericalRange_RadiusAffine
import Definitions.Def_Operator_Crouzeix_SpectralSetSuperset
set_option autoImplicit false
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem isKPolynomialSpectralSet_of_closure_numericalRange_subset
    (A : E →L[ℂ] E) {K : Set ℂ} (hK : IsCompact K)
    (hsub : closure (numericalRange A) ⊆ K) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2) K := by sorry

-- Prove2me | Theorems.Thm_crouzeix_palencia_of_closure_numericalRange_eq_smoothJordanClosure
-- name    : crouzeix_palencia_of_closure_numericalRange_eq_smoothJordanClosure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:05:51.809212+00:00
-- url     : https://prove2.me/theorems/4bb682ae-a58f-5a56-9353-517545f1d6d6
-- title:
--   crouzeix palencia of closure numerical Range eq smooth Jordan Closure: crouzeix palencia of closure numerical Range eq smooth Jordan Closure
-- statement:
--   If the closed numerical range is already the closed carrier of a smooth
--   convex Jordan domain, controlled inflation gives the exact
--   Crouzeix--Palencia spectral-set bound.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanInflation.lean#L98-L105
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanInflation.lean#L98-L105

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureAffine
import Definitions.Def_Operator_Crouzeix_SmoothJordanCompact
import Definitions.Def_Operator_Crouzeix_SmoothJordanOuterApproximation
import Definitions.Def_Operator_Crouzeix_SmoothJordanInflation
set_option autoImplicit false
open Complex Metric Set
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem crouzeix_palencia_of_closure_numericalRange_eq_smoothJordanClosure
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (hW : closure (numericalRange A) = closure Omega.carrier) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by sorry

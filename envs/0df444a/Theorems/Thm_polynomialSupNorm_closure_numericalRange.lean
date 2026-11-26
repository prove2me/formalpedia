-- Prove2me | Theorems.Thm_polynomialSupNorm_closure_numericalRange
-- name    : polynomialSupNorm_closure_numericalRange
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:43:44.44756+00:00
-- url     : https://prove2.me/theorems/31dcc9e6-156c-55b1-9c38-1dde6db81857
-- title:
--   polynomial Sup Norm closure numerical Range: polynomial Sup Norm closure numerical Range
-- statement:
--   Closing the numerical range does not alter a polynomial sup norm.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialBound.lean#L22-L26
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialBound.lean#L22-L26

import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_Operator_Crouzeix_BoundaryMaximum
import Definitions.Def_Operator_Crouzeix_SmoothSupportDomain
import Definitions.Def_Operator_Crouzeix_PolynomialBound
set_option autoImplicit false
open Complex Set
open scoped InnerProductSpace Polynomial
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem polynomialSupNorm_closure_numericalRange
    (A : E →L[ℂ] E) (p : ℂ[X]) :
    polynomialSupNorm p (closure (numericalRange A)) =
      polynomialSupNorm p (numericalRange A) := by sorry

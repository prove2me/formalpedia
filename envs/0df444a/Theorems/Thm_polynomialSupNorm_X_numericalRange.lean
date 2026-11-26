-- Prove2me | Theorems.Thm_polynomialSupNorm_X_numericalRange
-- name    : polynomialSupNorm_X_numericalRange
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:46:47.980062+00:00
-- url     : https://prove2.me/theorems/e62db447-cb12-4581-a8e1-bc22fab5624c
-- title:
--   polynomial Sup Norm X numerical Range: polynomial Sup Norm X numerical Range
-- statement:
--   The polynomial sup norm of `X` on the numerical range is the numerical
--   radius.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialBound.lean#L30-L33
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialBound.lean#L30-L33

import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_Operator_Crouzeix_BoundaryMaximum
import Definitions.Def_Operator_Crouzeix_SmoothSupportDomain
import Definitions.Def_Operator_Crouzeix_PolynomialBound
set_option autoImplicit false
open Complex Set
open scoped InnerProductSpace Polynomial
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem polynomialSupNorm_X_numericalRange (A : E →L[ℂ] E) :
    polynomialSupNorm Polynomial.X (numericalRange A) =
      numericalRadius A := by sorry

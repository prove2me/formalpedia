-- Prove2me | Theorems.Thm_norm_aeval_le_one_add_sqrt_two_mul_polynomialSupNorm_numericalRange
-- name    : norm_aeval_le_one_add_sqrt_two_mul_polynomialSupNorm_numericalRange
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:43:32.013433+00:00
-- url     : https://prove2.me/theorems/c4ed89d7-3a60-4ed7-a733-7e362203778c
-- title:
--   norm aeval le one add sqrt two mul polynomial Sup Norm numerical Range: norm aeval le one add sqrt two mul polynomial Sup Norm numerical Range
-- statement:
--   The usual norm form of the Crouzeix--Palencia theorem, with the supremum
--   taken directly over the numerical range.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialBound.lean#L49-L54
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialBound.lean#L49-L54

import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_Operator_Crouzeix_BoundaryMaximum
import Definitions.Def_Operator_Crouzeix_SmoothSupportDomain
import Definitions.Def_Operator_Crouzeix_PolynomialBound
set_option autoImplicit false
open Complex Set
open scoped InnerProductSpace Polynomial
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]

theorem norm_aeval_le_one_add_sqrt_two_mul_polynomialSupNorm_numericalRange
    (A : E →L[ℂ] E) (p : ℂ[X]) :
    ‖Polynomial.aeval A p‖ ≤
      (1 + Real.sqrt 2) * polynomialSupNorm p (numericalRange A) := by sorry

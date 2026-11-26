-- Prove2me | Theorems.Thm_norm_aeval_mul_aeval_le_one_add_sqrt_two_mul_iSup_numericalRange
-- name    : norm_aeval_mul_aeval_le_one_add_sqrt_two_mul_iSup_numericalRange
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:55:31.711358+00:00
-- url     : https://prove2.me/theorems/f2e363a1-c994-5168-89a3-d134907e8cd0
-- title:
--   norm aeval mul aeval le one add sqrt two mul i Sup numerical Range: norm aeval mul aeval le one add sqrt two mul i Sup numerical Range
-- statement:
--   A product of two polynomial functional-calculus values is controlled
--   with a single Crouzeix--Palencia constant.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialBound.lean#L176-L185
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialBound.lean#L176-L185

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

theorem norm_aeval_mul_aeval_le_one_add_sqrt_two_mul_iSup_numericalRange
    (A : E →L[ℂ] E) (p q : ℂ[X]) :
    ‖Polynomial.aeval A p * Polynomial.aeval A q‖ ≤
      (1 + Real.sqrt 2) *
        ⨆ z ∈ numericalRange A,
          ‖Polynomial.eval z p * Polynomial.eval z q‖ := by sorry

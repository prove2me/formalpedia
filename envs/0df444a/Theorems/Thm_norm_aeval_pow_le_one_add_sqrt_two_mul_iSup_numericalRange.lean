-- Prove2me | Theorems.Thm_norm_aeval_pow_le_one_add_sqrt_two_mul_iSup_numericalRange
-- name    : norm_aeval_pow_le_one_add_sqrt_two_mul_iSup_numericalRange
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:55:54.781385+00:00
-- url     : https://prove2.me/theorems/be011737-8dd3-49cf-9d38-722d0bc4b0d2
-- title:
--   norm aeval pow le one add sqrt two mul i Sup numerical Range: norm aeval pow le one add sqrt two mul i Sup numerical Range
-- statement:
--   Powers of a polynomial functional-calculus value retain a single
--   Crouzeix--Palencia constant.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialBound.lean#L189-L197
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialBound.lean#L189-L197

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

theorem norm_aeval_pow_le_one_add_sqrt_two_mul_iSup_numericalRange
    (A : E →L[ℂ] E) (p : ℂ[X]) (n : ℕ) :
    ‖Polynomial.aeval A p ^ n‖ ≤
      (1 + Real.sqrt 2) *
        ⨆ z ∈ numericalRange A, ‖Polynomial.eval z p ^ n‖ := by sorry

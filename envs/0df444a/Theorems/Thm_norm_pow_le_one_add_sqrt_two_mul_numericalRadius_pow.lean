-- Prove2me | Theorems.Thm_norm_pow_le_one_add_sqrt_two_mul_numericalRadius_pow
-- name    : norm_pow_le_one_add_sqrt_two_mul_numericalRadius_pow
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:43:26.557665+00:00
-- url     : https://prove2.me/theorems/e9d10fb4-fe8e-5195-a891-cc27fa114b5a
-- title:
--   norm pow le one add sqrt two mul numerical Radius pow: norm pow le one add sqrt two mul numerical Radius pow
-- statement:
--   Every operator power is controlled directly by the corresponding power
--   of the numerical radius with the Crouzeix--Palencia constant.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialBound.lean#L88-L93
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialBound.lean#L88-L93

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

theorem norm_pow_le_one_add_sqrt_two_mul_numericalRadius_pow
    (A : E →L[ℂ] E) (n : ℕ) :
    ‖A ^ n‖ ≤ (1 + Real.sqrt 2) * numericalRadius A ^ n := by sorry

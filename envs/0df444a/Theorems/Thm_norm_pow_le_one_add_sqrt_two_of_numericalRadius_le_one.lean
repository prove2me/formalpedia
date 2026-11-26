-- Prove2me | Theorems.Thm_norm_pow_le_one_add_sqrt_two_of_numericalRadius_le_one
-- name    : norm_pow_le_one_add_sqrt_two_of_numericalRadius_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:47:14.383812+00:00
-- url     : https://prove2.me/theorems/d6a740db-796b-5faa-a6b8-018f80ebd369
-- title:
--   norm pow le one add sqrt two of numerical Radius le one: norm pow le one add sqrt two of numerical Radius le one
-- statement:
--   Operators in the numerical-radius unit ball are uniformly power-bounded
--   by the Crouzeix--Palencia constant.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialBound.lean#L107-L115
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialBound.lean#L107-L115

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

theorem norm_pow_le_one_add_sqrt_two_of_numericalRadius_le_one
    (A : E →L[ℂ] E) (hA : numericalRadius A ≤ 1) (n : ℕ) :
    ‖A ^ n‖ ≤ 1 + Real.sqrt 2 := by sorry

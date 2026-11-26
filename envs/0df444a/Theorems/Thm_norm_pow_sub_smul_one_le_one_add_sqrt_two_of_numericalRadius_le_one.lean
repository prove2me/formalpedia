-- Prove2me | Theorems.Thm_norm_pow_sub_smul_one_le_one_add_sqrt_two_of_numericalRadius_le_one
-- name    : norm_pow_sub_smul_one_le_one_add_sqrt_two_of_numericalRadius_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:54:49.03387+00:00
-- url     : https://prove2.me/theorems/7197e0cc-d52c-5833-a9e9-9fa96b73e60f
-- title:
--   norm pow sub smul one le one add sqrt two of numerical Radius le one: norm pow sub smul one le one add sqrt two of numerical Radius le one
-- statement:
--   A centered operator in the numerical-radius unit ball is uniformly
--   power-bounded by the Crouzeix--Palencia constant.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialBound.lean#L119-L124
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialBound.lean#L119-L124

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

theorem norm_pow_sub_smul_one_le_one_add_sqrt_two_of_numericalRadius_le_one
    (A : E →L[ℂ] E) (c : ℂ)
    (hA : numericalRadius (A - c • (1 : E →L[ℂ] E)) ≤ 1) (n : ℕ) :
    ‖(A - c • (1 : E →L[ℂ] E)) ^ n‖ ≤ 1 + Real.sqrt 2 := by sorry

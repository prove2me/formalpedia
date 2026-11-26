-- Prove2me | Theorems.Thm_norm_le_one_add_sqrt_two_mul_numericalRadius
-- name    : norm_le_one_add_sqrt_two_mul_numericalRadius
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:46:38.255292+00:00
-- url     : https://prove2.me/theorems/6a5ec2ea-7c17-4a92-a850-6c93c487fb6c
-- title:
--   norm le one add sqrt two mul numerical Radius: norm le one add sqrt two mul numerical Radius
-- statement:
--   The Crouzeix--Palencia numerical-radius bound for an operator.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialBound.lean#L57-L63
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialBound.lean#L57-L63

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

theorem norm_le_one_add_sqrt_two_mul_numericalRadius
    (A : E →L[ℂ] E) :
    ‖A‖ ≤ (1 + Real.sqrt 2) * numericalRadius A := by sorry

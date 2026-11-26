-- Prove2me | Theorems.Thm_norm_pow_sub_smul_one_le_one_add_sqrt_two_mul_numericalRadius_pow
-- name    : norm_pow_sub_smul_one_le_one_add_sqrt_two_mul_numericalRadius_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:54:37.409783+00:00
-- url     : https://prove2.me/theorems/99c04bd3-4b8a-582d-ac02-d3fe4169e947
-- title:
--   norm pow sub smul one le one add sqrt two mul numerical Radius pow: norm pow sub smul one le one add sqrt two mul numerical Radius pow
-- statement:
--   Every centered operator power is controlled by the corresponding power
--   of its centered numerical radius.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialBound.lean#L97-L103
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialBound.lean#L97-L103

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

theorem norm_pow_sub_smul_one_le_one_add_sqrt_two_mul_numericalRadius_pow
    (A : E →L[ℂ] E) (c : ℂ) (n : ℕ) :
    ‖(A - c • (1 : E →L[ℂ] E)) ^ n‖ ≤
      (1 + Real.sqrt 2) *
        numericalRadius (A - c • (1 : E →L[ℂ] E)) ^ n := by sorry

-- Prove2me | Theorems.Thm_norm_sub_smul_one_le_one_add_sqrt_two_mul_numericalRadius
-- name    : norm_sub_smul_one_le_one_add_sqrt_two_mul_numericalRadius
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:54:37.605472+00:00
-- url     : https://prove2.me/theorems/9d62b93a-71ea-560b-9dcb-4e03d2789a8d
-- title:
--   norm sub smul one le one add sqrt two mul numerical Radius: norm sub smul one le one add sqrt two mul numerical Radius
-- statement:
--   The Crouzeix--Palencia numerical-radius bound centered at an arbitrary
--   scalar operator.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialBound.lean#L67-L73
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialBound.lean#L67-L73

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

theorem norm_sub_smul_one_le_one_add_sqrt_two_mul_numericalRadius
    (A : E →L[ℂ] E) (c : ℂ) :
    ‖A - c • (1 : E →L[ℂ] E)‖ ≤
      (1 + Real.sqrt 2) *
        numericalRadius (A - c • (1 : E →L[ℂ] E)) := by sorry

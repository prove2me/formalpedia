-- Prove2me | Theorems.Thm_norm_sub_smul_one_le_one_add_sqrt_two_mul_iSup_numericalRange
-- name    : norm_sub_smul_one_le_one_add_sqrt_two_mul_iSup_numericalRange
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:54:54.180247+00:00
-- url     : https://prove2.me/theorems/ca4c4bc1-5bbb-5b21-8b1b-5537ffcec629
-- title:
--   norm sub smul one le one add sqrt two mul i Sup numerical Range: norm sub smul one le one add sqrt two mul i Sup numerical Range
-- statement:
--   A centered form of the bound: the distance of `A` from a scalar operator
--   is controlled by the farthest point of its numerical range from that scalar.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialBound.lean#L153-L172
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialBound.lean#L153-L172

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

theorem norm_sub_smul_one_le_one_add_sqrt_two_mul_iSup_numericalRange
    (A : E →L[ℂ] E) (c : ℂ) :
    ‖A - c • (1 : E →L[ℂ] E)‖ ≤
      (1 + Real.sqrt 2) * ⨆ z ∈ numericalRange A, ‖z - c‖ := by sorry

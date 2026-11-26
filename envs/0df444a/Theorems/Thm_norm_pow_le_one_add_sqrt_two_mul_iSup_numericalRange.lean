-- Prove2me | Theorems.Thm_norm_pow_le_one_add_sqrt_two_mul_iSup_numericalRange
-- name    : norm_pow_le_one_add_sqrt_two_mul_iSup_numericalRange
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:46:33.779672+00:00
-- url     : https://prove2.me/theorems/43aa7d23-340a-5c43-93a9-7085c28dd540
-- title:
--   norm pow le one add sqrt two mul i Sup numerical Range: norm pow le one add sqrt two mul i Sup numerical Range
-- statement:
--   Every power of an operator is controlled by the corresponding power on
--   its numerical range.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialBound.lean#L77-L84
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialBound.lean#L77-L84

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

theorem norm_pow_le_one_add_sqrt_two_mul_iSup_numericalRange
    (A : E →L[ℂ] E) (n : ℕ) :
    ‖A ^ n‖ ≤
      (1 + Real.sqrt 2) * ⨆ z ∈ numericalRange A, ‖z ^ n‖ := by sorry

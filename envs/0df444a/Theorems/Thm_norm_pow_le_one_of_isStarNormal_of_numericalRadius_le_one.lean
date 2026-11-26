-- Prove2me | Theorems.Thm_norm_pow_le_one_of_isStarNormal_of_numericalRadius_le_one
-- name    : norm_pow_le_one_of_isStarNormal_of_numericalRadius_le_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:57:43.679515+00:00
-- url     : https://prove2.me/theorems/679fb06d-c3c9-47b0-88f6-f15f2c8598a8
-- title:
--   norm pow le one of is Star Normal of numerical Radius le one: norm pow le one of is Star Normal of numerical Radius le one
-- statement:
--   A normal operator in the numerical-radius unit ball is power-bounded by
--   one.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalPolynomialBound.lean#L78-L83
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalPolynomialBound.lean#L78-L83

import Definitions.Def_Operator_Crouzeix_PolynomialBound
import Definitions.Def_Operator_NumericalRange_RadiusNormal
import Definitions.Def_Operator_SpectralSet_Normal
import Definitions.Def_Operator_Crouzeix_NormalPolynomialBound
set_option autoImplicit false
open Complex Set
open scoped InnerProductSpace Polynomial
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem norm_pow_le_one_of_isStarNormal_of_numericalRadius_le_one
    (A : E →L[ℂ] E) [IsStarNormal A]
    (hA : numericalRadius A ≤ 1) (n : ℕ) :
    ‖A ^ n‖ ≤ 1 := by sorry

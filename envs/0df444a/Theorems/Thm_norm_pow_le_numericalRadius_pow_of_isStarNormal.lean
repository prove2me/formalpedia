-- Prove2me | Theorems.Thm_norm_pow_le_numericalRadius_pow_of_isStarNormal
-- name    : norm_pow_le_numericalRadius_pow_of_isStarNormal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:47:39.808528+00:00
-- url     : https://prove2.me/theorems/83a239e6-703c-5d12-b92a-7ecd9f3849b5
-- title:
--   norm pow le numerical Radius pow of is Star Normal: norm pow le numerical Radius pow of is Star Normal
-- statement:
--   Powers of a normal operator are bounded sharply by powers of its
--   numerical radius.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalPolynomialBound.lean#L68-L74
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalPolynomialBound.lean#L68-L74

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

theorem norm_pow_le_numericalRadius_pow_of_isStarNormal
    (A : E →L[ℂ] E) [IsStarNormal A] (n : ℕ) :
    ‖A ^ n‖ ≤ numericalRadius A ^ n := by sorry

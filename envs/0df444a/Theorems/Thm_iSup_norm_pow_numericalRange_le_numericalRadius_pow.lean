-- Prove2me | Theorems.Thm_iSup_norm_pow_numericalRange_le_numericalRadius_pow
-- name    : iSup_norm_pow_numericalRange_le_numericalRadius_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:44:04.049282+00:00
-- url     : https://prove2.me/theorems/9274d863-3105-5529-8d86-5ebd59b2bce4
-- title:
--   i Sup norm pow numerical Range le numerical Radius pow: i Sup norm pow numerical Range le numerical Radius pow
-- statement:
--   The supremum of the `n`th powers on the numerical range is bounded by
--   the `n`th power of the numerical radius.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialBound.lean#L37-L43
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialBound.lean#L37-L43

import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_Operator_Crouzeix_BoundaryMaximum
import Definitions.Def_Operator_Crouzeix_SmoothSupportDomain
import Definitions.Def_Operator_Crouzeix_PolynomialBound
set_option autoImplicit false
open Complex Set
open scoped InnerProductSpace Polynomial
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem iSup_norm_pow_numericalRange_le_numericalRadius_pow
    (A : E →L[ℂ] E) (n : ℕ) :
    (⨆ z ∈ numericalRange A, ‖z ^ n‖) ≤ numericalRadius A ^ n := by sorry

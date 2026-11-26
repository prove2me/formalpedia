-- Prove2me | Theorems.Thm_numericalRadius_pow_le_two_mul_pow
-- name    : numericalRadius_pow_le_two_mul_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:14:59.646061+00:00
-- url     : https://prove2.me/theorems/4e45f998-89e6-5325-b0f3-d0d0cf54ef10
-- title:
--   numerical Radius pow le two mul pow: numerical Radius pow le two mul pow
-- statement:
--   Powers are controlled by the power of twice the numerical radius.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAlgebra.lean#L57-L65
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAlgebra.lean#L57-L65

import Mathlib.Analysis.Normed.Operator.Mul
import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_NumericalRange_RadiusAlgebra
set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem numericalRadius_pow_le_two_mul_pow
    [Nontrivial E] (A : E →L[ℂ] E) (n : ℕ) :
    numericalRadius (A ^ n) ≤ (2 * numericalRadius A) ^ n := by sorry

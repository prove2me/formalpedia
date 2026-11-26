-- Prove2me | Theorems.Thm_numericalRadius_mul_le_four_mul
-- name    : numericalRadius_mul_le_four_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:22:42.298684+00:00
-- url     : https://prove2.me/theorems/bf0b54b6-d851-41e0-9ad9-5a425c5395f8
-- title:
--   numerical Radius mul le four mul: numerical Radius mul le four mul
-- statement:
--   Uniform quasi-submultiplicativity of numerical radius.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAlgebra.lean#L44-L54
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAlgebra.lean#L44-L54

import Mathlib.Analysis.Normed.Operator.Mul
import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_NumericalRange_RadiusAlgebra
set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem numericalRadius_mul_le_four_mul
    (A B : E →L[ℂ] E) :
    numericalRadius (A * B) ≤
      4 * numericalRadius A * numericalRadius B := by sorry

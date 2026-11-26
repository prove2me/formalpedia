-- Prove2me | Theorems.Thm_numericalRadius_mul_le_norm_mul_norm
-- name    : numericalRadius_mul_le_norm_mul_norm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:22:50.816972+00:00
-- url     : https://prove2.me/theorems/bf50cccb-5749-4276-8992-aff0d5f0b0d4
-- title:
--   numerical Radius mul le norm mul norm: numerical Radius mul le norm mul norm
-- statement:
--   The numerical radius of a product is bounded by the product of the
--   operator norms.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAlgebra.lean#L18-L21
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAlgebra.lean#L18-L21

import Mathlib.Analysis.Normed.Operator.Mul
import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_NumericalRange_RadiusAlgebra
set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem numericalRadius_mul_le_norm_mul_norm
    (A B : E →L[ℂ] E) :
    numericalRadius (A * B) ≤ ‖A‖ * ‖B‖ := by sorry

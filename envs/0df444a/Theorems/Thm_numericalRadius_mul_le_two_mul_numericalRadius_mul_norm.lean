-- Prove2me | Theorems.Thm_numericalRadius_mul_le_two_mul_numericalRadius_mul_norm
-- name    : numericalRadius_mul_le_two_mul_numericalRadius_mul_norm
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:27:24.164747+00:00
-- url     : https://prove2.me/theorems/e8492bfe-ce95-56f2-a4e8-959f0d35151d
-- title:
--   numerical Radius mul le two mul numerical Radius mul norm: numerical Radius mul le two mul numerical Radius mul norm
-- statement:
--   A product estimate using numerical radius in the left factor.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAlgebra.lean#L24-L29
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAlgebra.lean#L24-L29

import Mathlib.Analysis.Normed.Operator.Mul
import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_NumericalRange_RadiusAlgebra
set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem numericalRadius_mul_le_two_mul_numericalRadius_mul_norm
    (A B : E →L[ℂ] E) :
    numericalRadius (A * B) ≤ 2 * numericalRadius A * ‖B‖ := by sorry

-- Prove2me | Theorems.Thm_numericalRadius_mul_le_two_mul_norm_mul_numericalRadius
-- name    : numericalRadius_mul_le_two_mul_norm_mul_numericalRadius
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:15:02.314351+00:00
-- url     : https://prove2.me/theorems/1866f70c-6bbf-4f97-89bc-6880cf7ac1fa
-- title:
--   numerical Radius mul le two mul norm mul numerical Radius: numerical Radius mul le two mul norm mul numerical Radius
-- statement:
--   A product estimate using numerical radius in the right factor.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAlgebra.lean#L32-L41
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAlgebra.lean#L32-L41

import Mathlib.Analysis.Normed.Operator.Mul
import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_NumericalRange_RadiusAlgebra
set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem numericalRadius_mul_le_two_mul_norm_mul_numericalRadius
    (A B : E →L[ℂ] E) :
    numericalRadius (A * B) ≤ 2 * ‖A‖ * numericalRadius B := by sorry

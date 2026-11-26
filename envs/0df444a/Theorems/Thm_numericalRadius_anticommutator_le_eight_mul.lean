-- Prove2me | Theorems.Thm_numericalRadius_anticommutator_le_eight_mul
-- name    : numericalRadius_anticommutator_le_eight_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:15:20.688803+00:00
-- url     : https://prove2.me/theorems/c80d5247-0cf6-544b-a6d6-4ca1d4ebacd4
-- title:
--   numerical Radius anticommutator le eight mul: numerical Radius anticommutator le eight mul
-- statement:
--   The same uniform constant-eight bound holds for the anticommutator.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAlgebra.lean#L84-L96
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAlgebra.lean#L84-L96

import Mathlib.Analysis.Normed.Operator.Mul
import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_NumericalRange_RadiusAlgebra
set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem numericalRadius_anticommutator_le_eight_mul
    (A B : E →L[ℂ] E) :
    numericalRadius (A * B + B * A) ≤
      8 * numericalRadius A * numericalRadius B := by sorry

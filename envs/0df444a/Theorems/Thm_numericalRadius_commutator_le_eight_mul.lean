-- Prove2me | Theorems.Thm_numericalRadius_commutator_le_eight_mul
-- name    : numericalRadius_commutator_le_eight_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:15:08.921412+00:00
-- url     : https://prove2.me/theorems/7614452d-4d5e-5239-80a7-349e18ce2a65
-- title:
--   numerical Radius commutator le eight mul: numerical Radius commutator le eight mul
-- statement:
--   The numerical radius of a commutator has the uniform constant-eight
--   bound coming from quasi-submultiplicativity.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAlgebra.lean#L69-L81
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAlgebra.lean#L69-L81

import Mathlib.Analysis.Normed.Operator.Mul
import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_NumericalRange_RadiusAlgebra
set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem numericalRadius_commutator_le_eight_mul
    (A B : E →L[ℂ] E) :
    numericalRadius (A * B - B * A) ≤
      8 * numericalRadius A * numericalRadius B := by sorry

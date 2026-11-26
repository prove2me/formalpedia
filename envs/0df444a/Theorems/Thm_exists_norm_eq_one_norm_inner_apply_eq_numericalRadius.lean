-- Prove2me | Theorems.Thm_exists_norm_eq_one_norm_inner_apply_eq_numericalRadius
-- name    : exists_norm_eq_one_norm_inner_apply_eq_numericalRadius
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:15:52.728811+00:00
-- url     : https://prove2.me/theorems/76ff29b1-014a-5bd9-a0bf-58a022799bc7
-- title:
--   exists norm eq one norm inner apply eq numerical Radius: exists norm eq one norm inner apply eq numerical Radius
-- statement:
--   In finite dimension, a unit vector attains the numerical radius.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusFiniteDimensional.lean#L34-L40
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusFiniteDimensional.lean#L34-L40

import Definitions.Def_Operator_NumericalRange_Compact
import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_NumericalRange_RadiusFiniteDimensional
set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [Nontrivial E]

theorem exists_norm_eq_one_norm_inner_apply_eq_numericalRadius
    (A : E →L[ℂ] E) :
    ∃ x : E, ‖x‖ = 1 ∧ ‖⟪x, A x⟫_ℂ‖ = numericalRadius A := by sorry

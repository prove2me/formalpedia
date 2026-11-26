-- Prove2me | Theorems.Thm_exists_mem_numericalRange_norm_eq_numericalRadius
-- name    : exists_mem_numericalRange_norm_eq_numericalRadius
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:27:29.528316+00:00
-- url     : https://prove2.me/theorems/1ac7d9b1-faf2-533f-b6db-cbdca563ef2e
-- title:
--   exists mem numerical Range norm eq numerical Radius: exists mem numerical Range norm eq numerical Radius
-- statement:
--   In finite dimension, some point of the numerical range has modulus equal
--   to the numerical radius.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusFiniteDimensional.lean#L17-L31
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusFiniteDimensional.lean#L17-L31

import Definitions.Def_Operator_NumericalRange_Compact
import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_NumericalRange_RadiusFiniteDimensional
set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [Nontrivial E]

theorem exists_mem_numericalRange_norm_eq_numericalRadius
    (A : E →L[ℂ] E) :
    ∃ z ∈ numericalRange A, ‖z‖ = numericalRadius A := by sorry

-- Prove2me | Theorems.Thm_numericalRadius_eq_one_of_mem_unitary
-- name    : numericalRadius_eq_one_of_mem_unitary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:57:03.743187+00:00
-- url     : https://prove2.me/theorems/65683412-58bd-47ed-98da-6d2c5e004a0f
-- title:
--   numerical Radius eq one of mem unitary: numerical Radius eq one of mem unitary
-- statement:
--   A unitary operator on a nontrivial Hilbert space has numerical radius
--   one.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusNormal.lean#L41-L47
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusNormal.lean#L41-L47

import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Definitions.Def_Operator_NumericalRange_RadiusSpectrum
import Definitions.Def_Operator_NumericalRange_RadiusNormal
set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem numericalRadius_eq_one_of_mem_unitary
    [Nontrivial E] (U : E →L[ℂ] E)
    (hU : U ∈ unitary (E →L[ℂ] E)) :
    numericalRadius U = 1 := by sorry

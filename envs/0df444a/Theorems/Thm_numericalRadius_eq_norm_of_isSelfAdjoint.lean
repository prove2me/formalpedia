-- Prove2me | Theorems.Thm_numericalRadius_eq_norm_of_isSelfAdjoint
-- name    : numericalRadius_eq_norm_of_isSelfAdjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:24:16.611101+00:00
-- url     : https://prove2.me/theorems/8e195f82-300d-5e94-9145-40073ceb9623
-- title:
--   numerical Radius eq norm of is Self Adjoint: numerical Radius eq norm of is Self Adjoint
-- statement:
--   A selfadjoint operator has numerical radius equal to its norm.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusNormal.lean#L33-L37
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusNormal.lean#L33-L37

import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Definitions.Def_Operator_NumericalRange_RadiusSpectrum
import Definitions.Def_Operator_NumericalRange_RadiusNormal
set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem numericalRadius_eq_norm_of_isSelfAdjoint
    (A : E →L[ℂ] E) (hA : IsSelfAdjoint A) :
    numericalRadius A = ‖A‖ := by sorry

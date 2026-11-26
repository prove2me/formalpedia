-- Prove2me | Theorems.Thm_numericalRadius_eq_norm_of_isStarNormal
-- name    : numericalRadius_eq_norm_of_isStarNormal
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:18:47.461256+00:00
-- url     : https://prove2.me/theorems/5f2b8d6a-be75-4eea-93f5-9a8f0fc657eb
-- title:
--   numerical Radius eq norm of is Star Normal: numerical Radius eq norm of is Star Normal
-- statement:
--   The numerical radius of a normal operator equals its operator norm.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusNormal.lean#L18-L30
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusNormal.lean#L18-L30

import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Definitions.Def_Operator_NumericalRange_RadiusSpectrum
import Definitions.Def_Operator_NumericalRange_RadiusNormal
set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem numericalRadius_eq_norm_of_isStarNormal
    (A : E →L[ℂ] E) [IsStarNormal A] :
    numericalRadius A = ‖A‖ := by sorry

-- Prove2me | Theorems.Thm_closure_numericalRange_subset_closedBall_numericalRadius
-- name    : closure_numericalRange_subset_closedBall_numericalRadius
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:17:26.752801+00:00
-- url     : https://prove2.me/theorems/7ed6053b-0b1b-52a2-80f2-98dc41f69d38
-- title:
--   closure numerical Range subset closed Ball numerical Radius: closure numerical Range subset closed Ball numerical Radius
-- statement:
--   The closure of the numerical range remains in the closed disk determined
--   by the numerical radius.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusSpectrum.lean#L20-L27
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusSpectrum.lean#L20-L27

import Mathlib.Analysis.Normed.Algebra.Spectrum
import Definitions.Def_Operator_NumericalRange_Affine
import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Definitions.Def_Operator_NumericalRange_RadiusSpectrum
set_option autoImplicit false
open Set
open scoped ENNReal InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem closure_numericalRange_subset_closedBall_numericalRadius
    (A : E →L[ℂ] E) :
    closure (numericalRange A) ⊆ Metric.closedBall 0 (numericalRadius A) := by sorry

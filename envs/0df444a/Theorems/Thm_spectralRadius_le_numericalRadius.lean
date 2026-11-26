-- Prove2me | Theorems.Thm_spectralRadius_le_numericalRadius
-- name    : spectralRadius_le_numericalRadius
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:59:55.064449+00:00
-- url     : https://prove2.me/theorems/27b8fad4-0811-5e14-8d6d-e5b50243169c
-- title:
--   spectral Radius le numerical Radius: spectral Radius le numerical Radius
-- statement:
--   The spectral radius is bounded by the numerical radius.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusSpectrum.lean#L163-L169
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusSpectrum.lean#L163-L169

import Mathlib.Analysis.Normed.Algebra.Spectrum
import Definitions.Def_Operator_NumericalRange_Affine
import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Definitions.Def_Operator_NumericalRange_RadiusSpectrum
set_option autoImplicit false
open Set
open scoped ENNReal InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]

theorem spectralRadius_le_numericalRadius (A : E →L[ℂ] E) :
    spectralRadius ℂ A ≤ ENNReal.ofReal (numericalRadius A) := by sorry

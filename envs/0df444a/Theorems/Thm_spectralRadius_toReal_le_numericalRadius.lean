-- Prove2me | Theorems.Thm_spectralRadius_toReal_le_numericalRadius
-- name    : spectralRadius_toReal_le_numericalRadius
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:18:24.873803+00:00
-- url     : https://prove2.me/theorems/a044718c-7bd8-5fd8-8a2d-8532edf21bb1
-- title:
--   spectral Radius to Real le numerical Radius: spectral Radius to Real le numerical Radius
-- statement:
--   Real-valued form of `spectralRadius_le_numericalRadius`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusSpectrum.lean#L180-L188
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusSpectrum.lean#L180-L188

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

theorem spectralRadius_toReal_le_numericalRadius (A : E →L[ℂ] E) :
    (spectralRadius ℂ A).toReal ≤ numericalRadius A := by sorry

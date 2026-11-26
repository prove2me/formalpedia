-- Prove2me | Theorems.Thm_spectralRadius_sub_smul_one_toReal_le_centered_numericalRadius
-- name    : spectralRadius_sub_smul_one_toReal_le_centered_numericalRadius
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:56:57.854335+00:00
-- url     : https://prove2.me/theorems/cfdcc84c-3bf9-5ed7-b5f6-0b88bf60bd88
-- title:
--   spectral Radius sub smul one to Real le centered numerical Radius: spectral Radius sub smul one to Real le centered numerical Radius
-- statement:
--   Real-valued centered form of the spectral-radius bound.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusSpectrum.lean#L191-L196
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusSpectrum.lean#L191-L196

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

theorem spectralRadius_sub_smul_one_toReal_le_centered_numericalRadius
    (A : E →L[ℂ] E) (c : ℂ) :
    (spectralRadius ℂ (A - c • (1 : E →L[ℂ] E))).toReal ≤
      numericalRadius (A - c • (1 : E →L[ℂ] E)) := by sorry

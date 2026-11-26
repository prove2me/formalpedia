-- Prove2me | Theorems.Thm_spectrum_subset_closedBall_numericalRadius
-- name    : spectrum_subset_closedBall_numericalRadius
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:17:29.781677+00:00
-- url     : https://prove2.me/theorems/fbf577fa-847c-5564-ae0b-cf2b2bfe8623
-- title:
--   spectrum subset closed Ball numerical Radius: spectrum subset closed Ball numerical Radius
-- statement:
--   The spectrum is contained in the closed disk whose radius is the
--   numerical radius.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusSpectrum.lean#L83-L86
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusSpectrum.lean#L83-L86

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

theorem spectrum_subset_closedBall_numericalRadius (A : E →L[ℂ] E) :
    spectrum ℂ A ⊆ Metric.closedBall 0 (numericalRadius A) := by sorry

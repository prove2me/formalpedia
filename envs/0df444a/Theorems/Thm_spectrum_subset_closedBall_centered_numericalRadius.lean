-- Prove2me | Theorems.Thm_spectrum_subset_closedBall_centered_numericalRadius
-- name    : spectrum_subset_closedBall_centered_numericalRadius
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:22:33.706129+00:00
-- url     : https://prove2.me/theorems/ada4fd34-5737-4e26-9a59-8f96ac218f52
-- title:
--   spectrum subset closed Ball centered numerical Radius: spectrum subset closed Ball centered numerical Radius
-- statement:
--   The spectrum lies in the disk centered at `c` with radius `w(A-cI)`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusSpectrum.lean#L115-L119
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusSpectrum.lean#L115-L119

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

theorem spectrum_subset_closedBall_centered_numericalRadius
    (A : E →L[ℂ] E) (c : ℂ) :
    spectrum ℂ A ⊆ Metric.closedBall c (numericalRadius (A - c • 1)) := by sorry

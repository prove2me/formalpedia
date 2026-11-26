-- Prove2me | Theorems.Thm_spectrum_sub_smul_one_subset_closedBall_centered_numericalRadius
-- name    : spectrum_sub_smul_one_subset_closedBall_centered_numericalRadius
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:56:34.527797+00:00
-- url     : https://prove2.me/theorems/dfd3d6e2-801c-41a3-a75e-6bb3d2b3a2f3
-- title:
--   spectrum sub smul one subset closed Ball centered numerical Radius: spectrum sub smul one subset closed Ball centered numerical Radius
-- statement:
--   The spectrum of a centered operator lies in its zero-centered
--   numerical-radius disk.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusSpectrum.lean#L90-L96
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusSpectrum.lean#L90-L96

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

theorem spectrum_sub_smul_one_subset_closedBall_centered_numericalRadius
    (A : E →L[ℂ] E) (c : ℂ) :
    spectrum ℂ (A - c • (1 : E →L[ℂ] E)) ⊆
      Metric.closedBall 0
        (numericalRadius (A - c • (1 : E →L[ℂ] E))) := by sorry

-- Prove2me | Theorems.Thm_dist_le_centered_numericalRadius_of_mem_spectrum
-- name    : dist_le_centered_numericalRadius_of_mem_spectrum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:56:35.454424+00:00
-- url     : https://prove2.me/theorems/c34f3c34-783f-5658-bcea-09db0de9b454
-- title:
--   dist le centered numerical Radius of mem spectrum: dist le centered numerical Radius of mem spectrum
-- statement:
--   Every spectral value lies within `w(A-cI)` of the chosen center `c`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusSpectrum.lean#L122-L125
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusSpectrum.lean#L122-L125

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

theorem dist_le_centered_numericalRadius_of_mem_spectrum
    (A : E →L[ℂ] E) (c : ℂ) {z : ℂ} (hz : z ∈ spectrum ℂ A) :
    dist z c ≤ numericalRadius (A - c • 1) := by sorry

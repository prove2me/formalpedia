-- Prove2me | Theorems.Thm_norm_le_numericalRadius_of_mem_spectrum
-- name    : norm_le_numericalRadius_of_mem_spectrum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:17:31.403827+00:00
-- url     : https://prove2.me/theorems/7c1489b2-146f-4ed7-80c6-dec8861d9d5e
-- title:
--   norm le numerical Radius of mem spectrum: norm le numerical Radius of mem spectrum
-- statement:
--   Every spectral value has modulus at most the numerical radius.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusSpectrum.lean#L99-L103
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusSpectrum.lean#L99-L103

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

theorem norm_le_numericalRadius_of_mem_spectrum
    (A : E →L[ℂ] E) {z : ℂ} (hz : z ∈ spectrum ℂ A) :
    ‖z‖ ≤ numericalRadius A := by sorry

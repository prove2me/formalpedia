-- Prove2me | Theorems.Thm_norm_le_centered_numericalRadius_of_mem_spectrum_sub_smul_one
-- name    : norm_le_centered_numericalRadius_of_mem_spectrum_sub_smul_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:56:33.296929+00:00
-- url     : https://prove2.me/theorems/c1c729b0-9846-415a-a40d-abb695008d76
-- title:
--   norm le centered numerical Radius of mem spectrum sub smul one: norm le centered numerical Radius of mem spectrum sub smul one
-- statement:
--   Every spectral value of a centered operator has modulus at most its
--   centered numerical radius.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusSpectrum.lean#L107-L112
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusSpectrum.lean#L107-L112

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

theorem norm_le_centered_numericalRadius_of_mem_spectrum_sub_smul_one
    (A : E →L[ℂ] E) (c : ℂ) {z : ℂ}
    (hz : z ∈ spectrum ℂ (A - c • (1 : E →L[ℂ] E))) :
    ‖z‖ ≤ numericalRadius (A - c • (1 : E →L[ℂ] E)) := by sorry

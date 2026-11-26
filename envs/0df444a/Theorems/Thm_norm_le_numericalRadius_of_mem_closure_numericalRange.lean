-- Prove2me | Theorems.Thm_norm_le_numericalRadius_of_mem_closure_numericalRange
-- name    : norm_le_numericalRadius_of_mem_closure_numericalRange
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:22:14.146665+00:00
-- url     : https://prove2.me/theorems/24ab21ab-238c-5776-8729-a32e1c065ec1
-- title:
--   norm le numerical Radius of mem closure numerical Range: norm le numerical Radius of mem closure numerical Range
-- statement:
--   Every point of the closed numerical range has modulus at most the
--   numerical radius.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusSpectrum.lean#L41-L45
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusSpectrum.lean#L41-L45

import Mathlib.Analysis.Normed.Algebra.Spectrum
import Definitions.Def_Operator_NumericalRange_Affine
import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Definitions.Def_Operator_NumericalRange_RadiusSpectrum
set_option autoImplicit false
open Set
open scoped ENNReal InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem norm_le_numericalRadius_of_mem_closure_numericalRange
    (A : E →L[ℂ] E) {z : ℂ} (hz : z ∈ closure (numericalRange A)) :
    ‖z‖ ≤ numericalRadius A := by sorry

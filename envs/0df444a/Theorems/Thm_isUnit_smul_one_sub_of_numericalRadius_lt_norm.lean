-- Prove2me | Theorems.Thm_isUnit_smul_one_sub_of_numericalRadius_lt_norm
-- name    : isUnit_smul_one_sub_of_numericalRadius_lt_norm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:17:37.093401+00:00
-- url     : https://prove2.me/theorems/d68a1c0e-4396-569b-8fe2-6fe8db32ba6c
-- title:
--   is Unit smul one sub of numerical Radius lt norm: is Unit smul one sub of numerical Radius lt norm
-- statement:
--   Every scalar whose modulus is larger than the numerical radius belongs
--   to the resolvent set.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusSpectrum.lean#L129-L136
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusSpectrum.lean#L129-L136

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

theorem isUnit_smul_one_sub_of_numericalRadius_lt_norm
    (A : E →L[ℂ] E) {z : ℂ} (hz : numericalRadius A < ‖z‖) :
    IsUnit (z • (1 : E →L[ℂ] E) - A) := by sorry

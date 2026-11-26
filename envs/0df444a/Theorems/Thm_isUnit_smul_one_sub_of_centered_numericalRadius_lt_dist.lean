-- Prove2me | Theorems.Thm_isUnit_smul_one_sub_of_centered_numericalRadius_lt_dist
-- name    : isUnit_smul_one_sub_of_centered_numericalRadius_lt_dist
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:56:45.184328+00:00
-- url     : https://prove2.me/theorems/d602dbc9-9d4d-5d47-a0b4-646f502980e7
-- title:
--   is Unit smul one sub of centered numerical Radius lt dist: is Unit smul one sub of centered numerical Radius lt dist
-- statement:
--   More generally, a scalar outside the disk centered at `c` with radius
--   `w(A-cI)` belongs to the resolvent set of `A`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusSpectrum.lean#L140-L152
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusSpectrum.lean#L140-L152

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

theorem isUnit_smul_one_sub_of_centered_numericalRadius_lt_dist
    (A : E →L[ℂ] E) (c : ℂ) {z : ℂ}
    (hz : numericalRadius (A - c • 1) < dist z c) :
    IsUnit (z • (1 : E →L[ℂ] E) - A) := by sorry

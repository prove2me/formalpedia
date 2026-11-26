-- Prove2me | Theorems.Thm_isUnit_one_sub_of_numericalRadius_lt_one
-- name    : isUnit_one_sub_of_numericalRadius_lt_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:56:48.973741+00:00
-- url     : https://prove2.me/theorems/64e8a3c8-1223-5b3a-8507-cde82f0ef36f
-- title:
--   is Unit one sub of numerical Radius lt one: is Unit one sub of numerical Radius lt one
-- statement:
--   In particular, `1-A` is a unit whenever `w(A) < 1`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusSpectrum.lean#L155-L160
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusSpectrum.lean#L155-L160

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

theorem isUnit_one_sub_of_numericalRadius_lt_one
    (A : E →L[ℂ] E) (hA : numericalRadius A < 1) :
    IsUnit (1 - A) := by sorry

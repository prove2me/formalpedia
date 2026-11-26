-- Prove2me | Theorems.Thm_dist_le_centered_numericalRadius_of_mem_closure_numericalRange
-- name    : dist_le_centered_numericalRadius_of_mem_closure_numericalRange
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:56:26.447913+00:00
-- url     : https://prove2.me/theorems/6bacaf35-b2f2-479f-ad96-1c60cd7fc7a3
-- title:
--   dist le centered numerical Radius of mem closure numerical Range: dist le centered numerical Radius of mem closure numerical Range
-- statement:
--   Every point of the closed numerical range lies within `w(A-cI)` of the
--   chosen center `c`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusSpectrum.lean#L72-L77
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusSpectrum.lean#L72-L77

import Mathlib.Analysis.Normed.Algebra.Spectrum
import Definitions.Def_Operator_NumericalRange_Affine
import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Definitions.Def_Operator_NumericalRange_RadiusSpectrum
set_option autoImplicit false
open Set
open scoped ENNReal InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem dist_le_centered_numericalRadius_of_mem_closure_numericalRange
    (A : E →L[ℂ] E) (c : ℂ) {z : ℂ}
    (hz : z ∈ closure (numericalRange A)) :
    dist z c ≤ numericalRadius (A - c • 1) := by sorry

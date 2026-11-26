-- Prove2me | Theorems.Thm_norm_le_centered_numericalRadius_of_mem_closure_numericalRange_sub_smul_one
-- name    : norm_le_centered_numericalRadius_of_mem_closure_numericalRange_sub_smul_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:56:10.149861+00:00
-- url     : https://prove2.me/theorems/210a7ec9-2ccb-5bf3-9219-0e421b3a710e
-- title:
--   norm le centered numerical Radius of mem closure numerical Range sub smul one: norm le centered numerical Radius of mem closure numerical Range sub smul one
-- statement:
--   Every point in the closed numerical range of a centered operator has
--   modulus at most its centered numerical radius.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusSpectrum.lean#L49-L54
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusSpectrum.lean#L49-L54

import Mathlib.Analysis.Normed.Algebra.Spectrum
import Definitions.Def_Operator_NumericalRange_Affine
import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Definitions.Def_Operator_NumericalRange_RadiusSpectrum
set_option autoImplicit false
open Set
open scoped ENNReal InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem norm_le_centered_numericalRadius_of_mem_closure_numericalRange_sub_smul_one
    (A : E →L[ℂ] E) (c : ℂ) {z : ℂ}
    (hz : z ∈ closure (numericalRange (A - c • (1 : E →L[ℂ] E)))) :
    ‖z‖ ≤ numericalRadius (A - c • (1 : E →L[ℂ] E)) := by sorry

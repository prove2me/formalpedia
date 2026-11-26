-- Prove2me | Theorems.Thm_closure_numericalRange_sub_smul_one_subset_closedBall_centered_numericalRadius
-- name    : closure_numericalRange_sub_smul_one_subset_closedBall_centered_numericalRadius
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:55:47.451891+00:00
-- url     : https://prove2.me/theorems/54a55cad-7f9d-5eef-8a2e-bd3d16412497
-- title:
--   closure numerical Range sub smul one subset closed Ball centered numerical Radius: closure numerical Range sub smul one subset closed Ball centered numerical Radius
-- statement:
--   The closed numerical range of a centered operator lies in its
--   zero-centered numerical-radius disk.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusSpectrum.lean#L31-L37
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusSpectrum.lean#L31-L37

import Mathlib.Analysis.Normed.Algebra.Spectrum
import Definitions.Def_Operator_NumericalRange_Affine
import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Definitions.Def_Operator_NumericalRange_RadiusSpectrum
set_option autoImplicit false
open Set
open scoped ENNReal InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem closure_numericalRange_sub_smul_one_subset_closedBall_centered_numericalRadius
    (A : E →L[ℂ] E) (c : ℂ) :
    closure (numericalRange (A - c • (1 : E →L[ℂ] E))) ⊆
      Metric.closedBall 0
        (numericalRadius (A - c • (1 : E →L[ℂ] E))) := by sorry

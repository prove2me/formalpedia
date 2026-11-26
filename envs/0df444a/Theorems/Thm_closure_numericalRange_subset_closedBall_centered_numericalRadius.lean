-- Prove2me | Theorems.Thm_closure_numericalRange_subset_closedBall_centered_numericalRadius
-- name    : closure_numericalRange_subset_closedBall_centered_numericalRadius
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:17:32.715807+00:00
-- url     : https://prove2.me/theorems/c0b5ccbd-c802-400f-9b30-44c36cab5451
-- title:
--   closure numerical Range subset closed Ball centered numerical Radius: closure numerical Range subset closed Ball centered numerical Radius
-- statement:
--   Centering the operator at `c` gives a closed disk of radius `w(A-cI)`
--   that contains the closed numerical range of `A`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusSpectrum.lean#L58-L68
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusSpectrum.lean#L58-L68

import Mathlib.Analysis.Normed.Algebra.Spectrum
import Definitions.Def_Operator_NumericalRange_Affine
import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Definitions.Def_Operator_NumericalRange_RadiusSpectrum
set_option autoImplicit false
open Set
open scoped ENNReal InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem closure_numericalRange_subset_closedBall_centered_numericalRadius
    (A : E →L[ℂ] E) (c : ℂ) :
    closure (numericalRange A) ⊆
      Metric.closedBall c (numericalRadius (A - c • 1)) := by sorry

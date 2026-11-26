-- Prove2me | Theorems.Thm_spectrum_subset_closure_numericalRange
-- name    : spectrum_subset_closure_numericalRange
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:35:29.240907+00:00
-- url     : https://prove2.me/theorems/4aa73e42-903a-4888-bd61-b2515769c3ab
-- title:
--   spectrum subset closure numerical Range: spectrum subset closure numerical Range
-- statement:
--   The spectrum of `A` is contained in the closure of its numerical range.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/SpectralSet/SpectrumInNR.lean#L87-L107
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/SpectralSet/SpectrumInNR.lean#L87-L107

import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Operator.Banach
import Definitions.Def_Operator_NumericalRange_Helpers
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
set_option autoImplicit false
open scoped InnerProductSpace
open ContinuousLinearMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]

theorem spectrum_subset_closure_numericalRange (A : E →L[ℂ] E) :
    spectrum ℂ (A : E →L[ℂ] E) ⊆ closure (numericalRange A) := by sorry

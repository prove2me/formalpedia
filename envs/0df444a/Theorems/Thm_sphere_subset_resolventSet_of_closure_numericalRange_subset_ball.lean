-- Prove2me | Theorems.Thm_sphere_subset_resolventSet_of_closure_numericalRange_subset_ball
-- name    : sphere_subset_resolventSet_of_closure_numericalRange_subset_ball
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:59:50.094818+00:00
-- url     : https://prove2.me/theorems/9f1d4ff8-ae63-459f-b8fe-d157990fe785
-- title:
--   sphere subset resolvent Set of closure numerical Range subset ball: sphere subset resolvent Set of closure numerical Range subset ball
-- statement:
--   If the closure of the numerical range lies in the open disk `ball c R`, the circle
--   `sphere c R` lies in the resolvent set.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleKernel.lean#L35-L44
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleKernel.lean#L35-L44

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Definitions.Def_Operator_Crouzeix_CircleKernel
set_option autoImplicit false
open Complex Polynomial spectrum
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem sphere_subset_resolventSet_of_closure_numericalRange_subset_ball (A : E →L[ℂ] E)
    {c : ℂ} {R : ℝ} (hW : closure (numericalRange A) ⊆ Metric.ball c R) :
    Metric.sphere c R ⊆ resolventSet ℂ A := by sorry

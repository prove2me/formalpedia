-- Prove2me | Theorems.Thm_contourIntegral_const_mul_resolvent_sq_eq_zero_of_numericalRange
-- name    : contourIntegral_const_mul_resolvent_sq_eq_zero_of_numericalRange
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:04:34.260153+00:00
-- url     : https://prove2.me/theorems/106e0cf5-a1d4-46b4-92b6-d2e7ac40b568
-- title:
--   contour Integral const mul resolvent sq eq zero of numerical Range: contour Integral const mul resolvent sq eq zero of numerical Range
-- statement:
--   The contour Integral const mul resolvent sq eq zero of numerical Range construction uses the contour Integral const mul resolvent sq eq zero of numerical Range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ResolventContourHomotopy.lean#L269-L286
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ResolventContourHomotopy.lean#L269-L286

import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelWinding
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Definitions.Def_Operator_Crouzeix_ResolventContourHomotopy
set_option autoImplicit false
open Complex Filter MeasureTheory Metric Set spectrum
open scoped InnerProductSpace Interval Pointwise Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem contourIntegral_const_mul_resolvent_sq_eq_zero_of_numericalRange
    (B D : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (hOmega : closure (numericalRange B) ⊆ Omega.carrier) :
    contourIntegral (fun z : ℂ => D * resolvent B z ^ 2)
      Omega.boundaryParam = 0 := by sorry

-- Prove2me | Theorems.Thm_contourIntegral_resolvent_affineOperator_eq_of_boundary_subset_resolventSet
-- name    : contourIntegral_resolvent_affineOperator_eq_of_boundary_subset_resolventSet
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:42:34.710418+00:00
-- url     : https://prove2.me/theorems/b82168c1-4539-578e-b97f-14fc672e0d5b
-- title:
--   contour Integral resolvent affine Operator eq of boundary subset resolvent Set: contour Integral resolvent affine Operator eq of boundary subset resolvent Set
-- statement:
--   The contour Integral resolvent affine Operator eq of boundary subset resolvent Set construction uses the contour Integral resolvent affine Operator eq of boundary subset resolvent Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ResolventContourHomotopy.lean#L317-L341
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ResolventContourHomotopy.lean#L317-L341

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

theorem contourIntegral_resolvent_affineOperator_eq_of_boundary_subset_resolventSet
    (B D : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (hBD : Commute B D)
    (hres : ∀ r ∈ Icc (0 : ℝ) 1, ∀ t : ℝ,
      Omega.boundaryParam t ∈
        resolventSet ℂ (B + (r : ℂ) • D)) :
    contourIntegral (resolvent (B + D)) Omega.boundaryParam =
      contourIntegral (resolvent B) Omega.boundaryParam := by sorry

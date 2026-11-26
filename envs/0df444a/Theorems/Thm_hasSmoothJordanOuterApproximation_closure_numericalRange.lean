-- Prove2me | Theorems.Thm_hasSmoothJordanOuterApproximation_closure_numericalRange
-- name    : hasSmoothJordanOuterApproximation_closure_numericalRange
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:07:41.302187+00:00
-- url     : https://prove2.me/theorems/2784e63e-f705-42b4-be91-24039cf7b889
-- title:
--   has Smooth Jordan Outer Approximation closure numerical Range: has Smooth Jordan Outer Approximation closure numerical Range
-- statement:
--   The closed numerical range has arbitrarily tight smooth Jordan outer
--   approximations.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportExhaustion.lean#L62-L68
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportExhaustion.lean#L62-L68

import Definitions.Def_Operator_Crouzeix_SmoothSupportDomain
import Definitions.Def_Operator_Crouzeix_SmoothSupportExhaustion
set_option autoImplicit false
open Complex Metric Set
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [Nontrivial E]

theorem hasSmoothJordanOuterApproximation_closure_numericalRange
    (A : E →L[ℂ] E) :
    HasSmoothJordanOuterApproximation (closure (numericalRange A)) := by sorry

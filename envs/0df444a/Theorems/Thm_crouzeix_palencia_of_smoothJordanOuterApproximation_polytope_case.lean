-- Prove2me | Theorems.Thm_crouzeix_palencia_of_smoothJordanOuterApproximation_polytope_case
-- name    : crouzeix_palencia_of_smoothJordanOuterApproximation_polytope_case
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:57:14.089132+00:00
-- url     : https://prove2.me/theorems/b98c7513-f242-58ed-9862-17a60f7ad379
-- title:
--   crouzeix palencia of smooth Jordan Outer Approximation polytope case: crouzeix palencia of smooth Jordan Outer Approximation polytope case
-- statement:
--   It is enough to solve smooth outer approximation for full-dimensional
--   finite convex hulls in order to obtain the exact Crouzeix--Palencia bound.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanPolytopeReduction.lean#L67-L76
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanPolytopeReduction.lean#L67-L76

import Definitions.Def_Operator_Crouzeix_SmoothJordanOuterApproximationReduction
import Mathlib.Analysis.Normed.Affine.Convex
import Definitions.Def_Operator_Crouzeix_SmoothJordanPolytopeReduction
set_option autoImplicit false
open Complex Metric Set
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [Nontrivial E]

theorem crouzeix_palencia_of_smoothJordanOuterApproximation_polytope_case
    (A : E →L[ℂ] E)
    (hpoly : HasSmoothJordanOuterApproximationForPolytopes) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by sorry

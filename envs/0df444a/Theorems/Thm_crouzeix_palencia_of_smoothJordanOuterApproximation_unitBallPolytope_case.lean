-- Prove2me | Theorems.Thm_crouzeix_palencia_of_smoothJordanOuterApproximation_unitBallPolytope_case
-- name    : crouzeix_palencia_of_smoothJordanOuterApproximation_unitBallPolytope_case
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:06:34.017197+00:00
-- url     : https://prove2.me/theorems/c01b5902-4a8b-5e8b-855f-076c75370902
-- title:
--   crouzeix palencia of smooth Jordan Outer Approximation unit Ball Polytope case: crouzeix palencia of smooth Jordan Outer Approximation unit Ball Polytope case
-- statement:
--   The exact Crouzeix--Palencia bound follows once smooth outer
--   approximation is proved for finite convex hulls containing a unit disk.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanSimilarity.lean#L198-L204
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanSimilarity.lean#L198-L204

import Definitions.Def_Operator_Crouzeix_SmoothJordanAffine
import Definitions.Def_Operator_Crouzeix_SmoothJordanPolytopeReduction
import Definitions.Def_Operator_Crouzeix_SmoothJordanSimilarity
set_option autoImplicit false
open Complex Metric Set
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [Nontrivial E]

theorem crouzeix_palencia_of_smoothJordanOuterApproximation_unitBallPolytope_case
    (A : E →L[ℂ] E)
    (hunit : HasSmoothJordanOuterApproximationForUnitBallPolytopes) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by sorry

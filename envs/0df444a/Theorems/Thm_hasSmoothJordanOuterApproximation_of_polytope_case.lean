-- Prove2me | Theorems.Thm_hasSmoothJordanOuterApproximation_of_polytope_case
-- name    : hasSmoothJordanOuterApproximation_of_polytope_case
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:55:21.292341+00:00
-- url     : https://prove2.me/theorems/daa430d4-dd06-5349-87f3-a78c1e65e8a4
-- title:
--   has Smooth Jordan Outer Approximation of polytope case: has Smooth Jordan Outer Approximation of polytope case
-- statement:
--   The full smooth outer-approximation theorem reduces to the
--   full-dimensional convex-polytope case.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanPolytopeReduction.lean#L30-L58
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanPolytopeReduction.lean#L30-L58

import Definitions.Def_Operator_Crouzeix_SmoothJordanOuterApproximationReduction
import Mathlib.Analysis.Normed.Affine.Convex
import Definitions.Def_Operator_Crouzeix_SmoothJordanPolytopeReduction
set_option autoImplicit false
open Complex Metric Set
open scoped InnerProductSpace

theorem hasSmoothJordanOuterApproximation_of_polytope_case
    {K : Set ℂ} (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    (hKconvex : Convex ℝ K)
    (hpoly : HasSmoothJordanOuterApproximationForPolytopes) :
    HasSmoothJordanOuterApproximation K := by sorry

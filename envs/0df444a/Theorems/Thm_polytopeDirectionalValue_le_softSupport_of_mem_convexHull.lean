-- Prove2me | Theorems.Thm_polytopeDirectionalValue_le_softSupport_of_mem_convexHull
-- name    : polytopeDirectionalValue_le_softSupport_of_mem_convexHull
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:01:14.828844+00:00
-- url     : https://prove2.me/theorems/f66222ff-0a40-578e-9f53-c5424d0a29f5
-- title:
--   polytope Directional Value le soft Support of mem convex Hull: polytope Directional Value le soft Support of mem convex Hull
-- statement:
--   The soft support bound extends from the vertices to their real convex
--   hull.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolytopeSoftSupport.lean#L116-L141
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolytopeSoftSupport.lean#L116-L141

import Definitions.Def_Operator_Crouzeix_SmoothJordanPolytopeReduction
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupport
set_option autoImplicit false
open Complex Set
open scoped ContDiff

theorem polytopeDirectionalValue_le_softSupport_of_mem_convexHull
    {u : Finset ℂ} {z : ℂ} (hz : z ∈ convexHull ℝ (u : Set ℂ))
    {delta : ℝ} (hdelta : 0 < delta) (theta : ℝ) :
    polytopeDirectionalValue z theta ≤
      polytopeSoftSupport u delta theta := by sorry

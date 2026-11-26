-- Prove2me | Theorems.Thm_contDiff_polytopeDirectionalValue
-- name    : contDiff_polytopeDirectionalValue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:57:45.585777+00:00
-- url     : https://prove2.me/theorems/7aca88f4-9e94-4f8a-9721-ec4bddc82434
-- title:
--   cont Diff polytope Directional Value: cont Diff polytope Directional Value
-- statement:
--   A directional value is infinitely differentiable in its angle.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolytopeSoftSupport.lean#L67-L71
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolytopeSoftSupport.lean#L67-L71

import Definitions.Def_Operator_Crouzeix_SmoothJordanPolytopeReduction
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupport
set_option autoImplicit false
open Complex Set
open scoped ContDiff

theorem contDiff_polytopeDirectionalValue (z : ℂ) :
    ContDiff ℝ ∞ (polytopeDirectionalValue z) := by sorry

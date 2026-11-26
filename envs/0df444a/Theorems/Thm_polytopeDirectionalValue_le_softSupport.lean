-- Prove2me | Theorems.Thm_polytopeDirectionalValue_le_softSupport
-- name    : polytopeDirectionalValue_le_softSupport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:57:46.097469+00:00
-- url     : https://prove2.me/theorems/a7fbd02c-5f3a-4afa-a944-8d170c4f6b91
-- title:
--   polytope Directional Value le soft Support: polytope Directional Value le soft Support
-- statement:
--   Log-sum-exp dominates each individual vertex support value.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolytopeSoftSupport.lean#L91-L112
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolytopeSoftSupport.lean#L91-L112

import Definitions.Def_Operator_Crouzeix_SmoothJordanPolytopeReduction
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupport
set_option autoImplicit false
open Complex Set
open scoped ContDiff

theorem polytopeDirectionalValue_le_softSupport
    {u : Finset ℂ} {z : ℂ} (hz : z ∈ u) {delta : ℝ}
    (hdelta : 0 < delta) (theta : ℝ) :
    polytopeDirectionalValue z theta ≤
      polytopeSoftSupport u delta theta := by sorry

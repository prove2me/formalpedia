-- Prove2me | Theorems.Thm_polytopeSoftSupport_le_of_forall_directionalValue_le
-- name    : polytopeSoftSupport_le_of_forall_directionalValue_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:03:35.63729+00:00
-- url     : https://prove2.me/theorems/5a3421e3-ac9d-43b5-8a7e-ea63a70892d4
-- title:
--   polytope Soft Support le of forall directional Value le: polytope Soft Support le of forall directional Value le
-- statement:
--   If `M` bounds every vertex in one direction, log-sum-exp exceeds `M` by
--   at most `delta * log(card u)`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolytopeSoftSupport.lean#L145-L178
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolytopeSoftSupport.lean#L145-L178

import Definitions.Def_Operator_Crouzeix_SmoothJordanPolytopeReduction
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupport
set_option autoImplicit false
open Complex Set
open scoped ContDiff

theorem polytopeSoftSupport_le_of_forall_directionalValue_le
    {u : Finset ℂ} (hu : u.Nonempty) {delta : ℝ} (hdelta : 0 < delta)
    (theta M : ℝ)
    (hM : ∀ z ∈ u, polytopeDirectionalValue z theta ≤ M) :
    polytopeSoftSupport u delta theta ≤
      M + delta * Real.log (u.card : ℝ) := by sorry

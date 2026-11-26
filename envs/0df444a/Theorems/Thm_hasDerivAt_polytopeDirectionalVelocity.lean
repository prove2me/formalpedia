-- Prove2me | Theorems.Thm_hasDerivAt_polytopeDirectionalVelocity
-- name    : hasDerivAt_polytopeDirectionalVelocity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:00:36.886373+00:00
-- url     : https://prove2.me/theorems/3704dc33-536c-4d06-b4ee-3d8342605d45
-- title:
--   has Deriv At polytope Directional Velocity: has Deriv At polytope Directional Velocity
-- statement:
--   The angular velocity differentiates to minus the directional value.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolytopeSoftSupportCurvature.lean#L83-L95
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolytopeSoftSupportCurvature.lean#L83-L95

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupport
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
set_option autoImplicit false
open Complex Set
open scoped ContDiff

theorem hasDerivAt_polytopeDirectionalVelocity (z : ℂ) (theta : ℝ) :
    HasDerivAt (polytopeDirectionalVelocity z)
      (-polytopeDirectionalValue z theta) theta := by sorry
